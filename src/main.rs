//! sqldance: choreograph SQL statements over several connections
//!
//! See README for details.

// XXX-dap TODO
// - colors
// - be able to move on when one query hangs
// - mode that single-steps anyway
// - tests

use anyhow::{bail, Context};
use camino::Utf8PathBuf;
use clap::Parser;
use newtype_derive::{NewtypeDeref, NewtypeFrom};
use postgres::{types::Type, GenericClient, NoTls};
use slog_error_chain::InlineErrorChain;
use std::{collections::BTreeMap, time::Duration};

/// Maximum number of connections allowed
///
/// This is just for safety.  If someone accidentally gives us garbage input,
/// let's not overwhelm the database.
///
/// Really, who needs more than *six* concurrent transactions to demonstrate
/// some behavior?
const MAX_CONNS: usize = 6;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Default `statement_timeout` for connections
    ///
    /// Can be overridden within a connection by issuing a `SET
    /// statement_timeout = N` query.
    ///
    /// Set to 0 to disable statement timeouts.
    #[arg(short = 't', long, default_value_t = 3_000)]
    statement_timeout_ms: u64,

    /// URL for database connections
    db_url: String,

    /// Input filename
    input_file: Utf8PathBuf,
}

fn main() {
    let args = Args::parse();

    if let Err(error) = sqldance(&args) {
        eprintln!("error: {:#}", error);
        std::process::exit(1);
    }
}

/// Runs the `sqldance` command using the given database params and input file
fn sqldance(args: &Args) -> anyhow::Result<()> {
    let file_contents = std::fs::read_to_string(&args.input_file)
        .with_context(|| format!("reading {:?}", args.input_file))?;
    let commands = parse_commands(&file_contents)
        .with_context(|| format!("parse {:?}", args.input_file))?;
    let statement_timeout = Duration::from_millis(args.statement_timeout_ms);
    let mut dance = Sqldance::new(&commands, &args.db_url, statement_timeout)?;
    for cmd in &commands {
        dance.run_one(cmd);
    }

    Ok(())
}

/// User-defined identifier for a connection (newtype around a `String`)
#[derive(Clone, Debug, Ord, PartialOrd, Eq, PartialEq)]
struct ConnId(String);
NewtypeFrom! { () struct ConnId(String); }
NewtypeDeref! { () struct ConnId(String); }

/// Describes one SQL query to execute using a specific connection
struct Command {
    /// which connection
    conn_id: ConnId,
    /// what command to execute
    sql: String,
}

/// Given the contents of an input file, parse out the sequence of commands
fn parse_commands(file_contents: &str) -> anyhow::Result<Vec<Command>> {
    let mut rv = Vec::new();
    #[derive(Debug, Eq, PartialEq)]
    enum ParseState {
        Init,
        ExpectCommandOrContinuation { conn_id: ConnId, sql: String },
    }
    let mut parse_state = ParseState::Init;
    for (i, line) in file_contents.lines().enumerate() {
        let line_num = i + 1;
        if let ParseState::ExpectCommandOrContinuation { conn_id, sql } =
            parse_state
        {
            if line.starts_with(|s: char| s.is_whitespace()) {
                parse_state = ParseState::ExpectCommandOrContinuation {
                    conn_id,
                    sql: format!("{}\n{}", sql, line),
                };
                continue;
            }

            rv.push(Command { conn_id, sql });
            parse_state = ParseState::Init;
        }

        assert_eq!(ParseState::Init, parse_state);
        if line.starts_with("#") {
            continue;
        }

        if line.trim().is_empty() {
            continue;
        }

        let mut parts = line.splitn(2, ":");
        match (parts.next(), parts.next()) {
            (None, n) => {
                assert_eq!(n, None);
                bail!("line {}: garbled", line_num);
            }
            (Some(_), None) => {
                bail!("line {}: expected ':'", line_num);
            }
            (Some(conn_id), Some(sql)) => {
                parse_state = ParseState::ExpectCommandOrContinuation {
                    conn_id: ConnId::from(conn_id.to_owned()),
                    sql: sql.trim().to_owned(),
                };
            }
        };
    }

    if let ParseState::ExpectCommandOrContinuation { conn_id, sql } =
        parse_state
    {
        rv.push(Command { conn_id, sql });
    }

    Ok(rv)
}

/// Tracks information associated with the user-defined connections
struct Sqldance {
    conns: BTreeMap<ConnId, Connection>,
}

impl Sqldance {
    /// Identify distinct connection ids referenced in `commands` and create a
    /// database connection for each one
    fn new(
        commands: &[Command],
        db_url: &str,
        statement_timeout: Duration,
    ) -> anyhow::Result<Sqldance> {
        let mut conns = BTreeMap::new();
        for c in commands {
            let conn_id = &c.conn_id;
            if conns.contains_key(conn_id) {
                continue;
            }

            if conns.len() == MAX_CONNS {
                bail!("only {:?} connections are allowed", MAX_CONNS);
            }

            let label = conn_id.to_string();
            eprint!("conn {:?}: connecting to {} ... ", label, db_url);
            let mut client = postgres::Client::connect(db_url, NoTls)
                .with_context(|| {
                    format!("connecting to database {:?}", db_url)
                })?;
            eprintln!("connected");
            client
                .execute(
                    "SET statement_timeout = $1",
                    &[&statement_timeout.as_millis().to_string()],
                )
                .with_context(|| {
                    format!(
                        "setting statement_timeout to {:?}",
                        statement_timeout
                    )
                })?;
            conns.insert(conn_id.clone(), Connection { label, client });
        }

        Ok(Sqldance { conns })
    }

    /// Run one command from the input file and print the results
    fn run_one(&mut self, cmd: &Command) {
        let conn = self.conns.get_mut(&cmd.conn_id).unwrap_or_else(|| {
            panic!("internal error: no connection for {:?}", cmd.conn_id)
        });
        conn.query_start(&cmd.sql);
        let client = &mut conn.client;
        match client.query(&cmd.sql, &[]) {
            Ok(rows) => {
                conn.query_rows(rows);
            }
            Err(error) => {
                conn.query_error(error);
            }
        }
        println!();
    }
}

/// Describes a distinct connection
struct Connection {
    /// user's name for this connection
    label: String,
    /// database connection
    client: postgres::Client,
}

impl Connection {
    /// Report that we're about to start running SQL
    fn query_start(&self, sql: &str) {
        println!("conn {:?}: executing: {:?}", self.label, sql);
    }

    /// Report the results of a successful query
    fn query_rows(&self, rows: Vec<postgres::Row>) {
        println!(
            "conn {:?}: success (rows returned: {})",
            self.label,
            rows.len()
        );

        if rows.is_empty() {
            return;
        }

        let column_names: Vec<_> =
            rows[0].columns().iter().map(|c| c.name().to_owned()).collect();
        let mut table_rows = Vec::with_capacity(rows.len() + 1);
        table_rows.push(column_names);
        for row in rows {
            let mut table_row = Vec::with_capacity(row.columns().len());
            for (i, c) in row.columns().iter().enumerate() {
                table_row.push(sql_render(&row, i, c.type_()));
            }
            table_rows.push(table_row);
        }

        let mut table = tabled::Table::from_iter(table_rows);
        table
            .with(tabled::settings::Style::modern())
            .with(tabled::settings::Padding::new(1, 1, 0, 0));
        println!("{}", table);
    }

    /// Report a failed query
    fn query_error(&self, error: postgres::Error) {
        println!(
            "conn {:?}: error: {}",
            self.label,
            InlineErrorChain::new(&error)
        );
    }
}

/// Renders one cell in a table describing a result set
///
/// * `row` is the SQL row
/// * `idx` is the index into that row
/// * `sql_type` is the type of that column
fn sql_render(row: &postgres::Row, idx: usize, sql_type: &Type) -> String {
    // This mapping between SQL types and Rust types comes from the docs for the
    // `postgres::types::FromSql`, though the types there don't match the
    // constants in postgres::types::Type.
    if *sql_type == Type::BOOL {
        sql_render_value::<bool>(row.try_get(idx))
    } else if *sql_type == Type::INT8 {
        sql_render_value::<i64>(row.try_get(idx))
    } else if *sql_type == Type::INT4 {
        sql_render_value::<i32>(row.try_get(idx))
    } else if *sql_type == Type::INT2 {
        sql_render_value::<i16>(row.try_get(idx))
    } else if *sql_type == Type::CHAR {
        sql_render_value::<i8>(row.try_get(idx))
    } else if *sql_type == Type::TEXT {
        sql_render_value::<String>(row.try_get(idx))
    } else if *sql_type == Type::UUID {
        sql_render_value::<uuid::Uuid>(row.try_get(idx))
    } else if *sql_type == Type::TIMESTAMP || *sql_type == Type::TIMESTAMPTZ {
        sql_render_value::<chrono::DateTime<chrono::Utc>>(row.try_get(idx))
    } else {
        String::from("<unsupported type>")
    }
}

/// Renders one Rust value that we tried to convert from its SQL value
///
/// This is a separate function for convenience because the caller can easily
/// specify what Rust type they want to use to convert the value.
fn sql_render_value<T: ToString>(t: Result<T, postgres::Error>) -> String {
    match t {
        Ok(t) => t.to_string(),
        Err(e) => format!("<bad conversion: {}>", InlineErrorChain::new(&e)),
    }
}

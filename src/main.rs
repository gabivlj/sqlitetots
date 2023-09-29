mod parser;
mod sql;

use anyhow::Result;

use clap::Parser;

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// SQL File to read from
    #[arg(short, long)]
    sql_file: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let file = std::fs::read_to_string(args.sql_file)?;
    sql::generate_typescript_types(&file)?;
    Ok(())
}

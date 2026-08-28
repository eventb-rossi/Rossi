use std::process::ExitCode;

use clap::{CommandFactory, Parser, Subcommand};

mod commands {
    pub mod build;
    pub mod build_common;
    pub mod completions;
    pub mod eventb_io;
    pub mod export;
    pub mod fmt;
    pub mod import;
    pub mod proofs;
    pub mod prove;
    pub mod sarif;
    pub mod style;
    pub mod validate;
}

#[derive(Parser)]
#[command(
    name = "rossi",
    version,
    propagate_version = true,
    about = "Rossi command-line tools for Event-B models"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Validate Event-B text files or Rodin ZIP archives.
    #[command(about = "Validate Event-B model files")]
    Validate(commands::validate::ValidateArgs),
    /// Import Rodin archives (.zip/.buc/.bum/dir) into Event-B text.
    #[command(about = "Import Rodin archives into Event-B text")]
    Import(commands::import::ImportArgs),
    /// Export Event-B text (.eventb/.txt/dir) into a Rodin .zip archive.
    #[command(about = "Export Event-B text into a Rodin .zip archive")]
    Export(commands::export::ExportArgs),
    /// Reformat Event-B text/archives in place (operator convention, indentation).
    #[command(about = "Reformat Event-B text/archives in place")]
    Fmt(commands::fmt::FmtArgs),
    /// Static-check a Rodin project and emit `.bcc` / `.bcm` output.
    #[command(about = "Static-check a Rodin project and emit .bcc/.bcm output")]
    Build(commands::build::BuildArgs),
    /// Check the stored proofs of an Event-B project against its
    /// obligations.
    #[command(about = "Check stored proofs against their proof obligations")]
    Prove(commands::prove::ProveArgs),
    /// Generate a shell completion script (bash, zsh, fish, …).
    #[command(about = "Generate a shell completion script")]
    Completions(commands::completions::CompletionsArgs),
}

fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Validate(args) => commands::validate::run(args),
        Command::Import(args) => commands::import::run(args),
        Command::Export(args) => commands::export::run(args),
        Command::Fmt(args) => commands::fmt::run(args),
        Command::Build(args) => commands::build::run_build_command(args),
        Command::Prove(args) => commands::prove::run(args),
        // Derive the completion script from the same clap command tree the CLI
        // parses with, so it can never drift from the real interface.
        Command::Completions(args) => commands::completions::run(args, &mut Cli::command()),
    }
}

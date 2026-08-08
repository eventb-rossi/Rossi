//! Typed formula objects for the Event-B mathematical language.
//!
//! This module is the successor to the name-based formula types in
//! [`crate::ast`]: immutable nodes classified by stable numeric tags
//! ([`tag`]), bound identifiers referenced by de Bruijn index, and types
//! attached directly to expression nodes. It is built up alongside the
//! existing AST and is not yet wired into the parser.

pub mod tag;
pub mod typenv;
pub mod types;

pub use typenv::{SealedTypeEnvironment, TypeEnvironmentBuilder};
pub use types::Type;

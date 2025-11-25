//! # Quantum Compiler
//!
//! Compiler for the Quantum smart contract language.
//!
//! This crate provides:
//! - Lexer and parser for Quantum source code
//! - Type checker with linear type system
//! - Borrow checker for resource safety
//! - Bytecode generator
//! - Optimization passes

#![warn(missing_docs, rust_2018_idioms)]
#![forbid(unsafe_code)]

pub mod lexer;
pub mod parser;
pub mod type_checker;
pub mod borrow_checker;
pub mod codegen;

pub use lexer::{Lexer, Token, TokenType, Location};
pub use parser::{Parser, AST, Module, Function, StructDef, Type, Expression, Statement};
pub use type_checker::{TypeChecker, TypeError};
pub use borrow_checker::{BorrowChecker, BorrowError};
pub use codegen::{CodeGenerator, CodeGenError};

// Re-export bytecode types from quantum-vm
pub use quantum_vm::bytecode;

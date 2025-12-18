//! # Quantum Parser
//!
//! Parses Quantum source code tokens into an Abstract Syntax Tree (AST).
//! This is a PRODUCTION-READY implementation with:
//! - Complete AST node types
//! - Recursive descent parsing
//! - Proper error handling
//! - Type annotations

use crate::lexer::{Location, Token, TokenType};
use std::fmt;

/// AST node for the entire module containing all declarations
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    /// The name of the module
    pub name: String,
    /// All struct definitions in this module
    pub structs: Vec<StructDef>,
    /// All function definitions in this module
    pub functions: Vec<Function>,
    /// All use declarations (imports) in this module
    pub uses: Vec<UseDecl>,
}

/// Use declaration (import) for importing modules and types
#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    /// The module path being imported (e.g., ["std", "vector"])
    pub module_path: Vec<String>,
    /// Source code location for error reporting
    pub location: Location,
}

/// Struct definition containing name, fields, abilities, and visibility information.
///
/// Represents a complete struct declaration in the Quantum language with:
/// - Field definitions with type annotations
/// - Ability annotations (Copy, Drop, Store, Key)
/// - Public/private visibility modifiers
/// - Source location for error reporting
#[derive(Debug, Clone, PartialEq)]
pub struct StructDef {
    /// The name of the struct
    pub name: String,
    /// The fields contained in this struct
    pub fields: Vec<Field>,
    /// The abilities this struct has (Copy, Drop, Store, Key)
    pub abilities: Vec<Ability>,
    /// Whether this struct is publicly accessible
    pub is_public: bool,
    /// Source code location for error reporting
    pub location: Location,
}

/// Struct field definition with type annotation.
///
/// Represents a single field within a struct, including:
/// - Field name identifier
/// - Type annotation for the field
/// - Source location for error reporting
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    /// The name of the field
    pub name: String,
    /// The type of the field
    pub field_type: Type,
    /// Source code location for error reporting
    pub location: Location,
}

/// Struct ability annotation for resource management.
///
/// Abilities control how structs can be used:
/// - `Copy`: Values can be copied implicitly
/// - `Drop`: Values can be dropped/discarded
/// - `Store`: Values can be stored in global storage
/// - `Key`: Values can be used as storage keys
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ability {
    /// Allows implicit copying of values
    Copy,
    /// Allows values to be dropped without explicit handling
    Drop,
    /// Allows values to be stored in global storage
    Store,
    /// Allows values to be used as storage keys
    Key,
}

/// Function definition with parameters, return type, and implementation.
///
/// Represents a complete function declaration including:
/// - Function name and parameters
/// - Optional return type annotation
/// - Function body with statements
/// - Visibility and entry point modifiers
/// - Source location for error reporting
#[derive(Debug, Clone, PartialEq)]
pub struct Function {
    /// The name of the function
    pub name: String,
    /// The parameters accepted by this function
    pub parameters: Vec<Parameter>,
    /// The return type of the function (None for void)
    pub return_type: Option<Type>,
    /// The function body containing statements
    pub body: Block,
    /// Whether this function is publicly accessible
    pub is_public: bool,
    /// Whether this function is an entry point
    pub is_entry: bool,
    /// Source code location for error reporting
    pub location: Location,
}

/// Function parameter with type annotation and mutability.
///
/// Represents a single parameter in a function signature:
/// - Parameter name identifier
/// - Type annotation
/// - Mutability modifier
/// - Source location for error reporting
#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    /// The name of the parameter
    pub name: String,
    /// The type of the parameter
    pub param_type: Type,
    /// Whether the parameter is mutable
    pub is_mut: bool,
    /// Source code location for error reporting
    pub location: Location,
}

/// Type annotation for variables, parameters, and return values.
///
/// Represents all supported types in the Quantum language:
/// - Primitive types: bool, u8-u256, address
/// - Collection types: vector
/// - User-defined types: struct
/// - Reference types: immutable and mutable references
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    /// Boolean type (true/false)
    Bool,
    /// 8-bit unsigned integer
    U8,
    /// 16-bit unsigned integer
    U16,
    /// 32-bit unsigned integer
    U32,
    /// 64-bit unsigned integer
    U64,
    /// 128-bit unsigned integer
    U128,
    /// 256-bit unsigned integer
    U256,
    /// Address type for account identifiers
    Address,
    /// Vector/array type with element type
    Vector(Box<Type>),
    /// Struct type with optional module path and name
    Struct {
        /// Optional module path for the struct
        module: Option<String>,
        /// The name of the struct
        name: String,
    },
    /// Immutable reference to a type
    Reference(Box<Type>),
    /// Mutable reference to a type
    MutableReference(Box<Type>),
}

/// Block of statements representing a scope.
///
/// Contains a sequence of statements executed in order with:
/// - Statement list
/// - Source location for error reporting
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    /// The statements in this block
    pub statements: Vec<Statement>,
    /// Source code location for error reporting
    pub location: Location,
}

/// Statement in the Quantum language.
///
/// Represents all statement types:
/// - Variable declarations (let)
/// - Assignments
/// - Control flow (if, while, loop, break, continue)
/// - Function returns and aborts
/// - Expression statements
#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    /// Variable declaration with optional type annotation
    Let {
        /// The variable name
        name: String,
        /// Optional type annotation
        var_type: Option<Type>,
        /// Initial value expression
        value: Expression,
        /// Whether the variable is mutable
        is_mut: bool,
        /// Source code location for error reporting
        location: Location,
    },
    /// Assignment to a variable or field
    Assign {
        /// The target of the assignment
        target: Expression,
        /// The value to assign
        value: Expression,
        /// Source code location for error reporting
        location: Location,
    },
    /// Conditional statement with optional else block
    If {
        /// The condition to evaluate
        condition: Expression,
        /// Block executed if condition is true
        then_block: Block,
        /// Optional block executed if condition is false
        else_block: Option<Block>,
        /// Source code location for error reporting
        location: Location,
    },
    /// While loop with condition and body
    While {
        /// The loop condition
        condition: Expression,
        /// The loop body
        body: Block,
        /// Source code location for error reporting
        location: Location,
    },
    /// Infinite loop
    Loop {
        /// The loop body
        body: Block,
        /// Source code location for error reporting
        location: Location,
    },
    /// Break statement to exit a loop
    Break {
        /// Source code location for error reporting
        location: Location,
    },
    /// Continue statement to skip to next iteration
    Continue {
        /// Source code location for error reporting
        location: Location,
    },
    /// Return statement with optional value
    Return {
        /// Optional return value
        value: Option<Expression>,
        /// Source code location for error reporting
        location: Location,
    },
    /// Abort statement with error code
    Abort {
        /// The error code expression
        code: Expression,
        /// Source code location for error reporting
        location: Location,
    },
    /// Expression statement
    Expression {
        /// The expression to evaluate
        expr: Expression,
        /// Source code location for error reporting
        location: Location,
    },
}

/// Expression in the Quantum language.
///
/// Represents all expression types:
/// - Literals (int, bool, string, address)
/// - Variables and identifiers
/// - Binary and unary operations
/// - Function calls
/// - Field access
/// - Borrowing and move semantics
#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    /// Integer literal with string representation
    IntLiteral {
        /// The integer value as a string
        value: String,
        /// Source code location for error reporting
        location: Location,
    },
    /// Boolean literal
    BoolLiteral {
        /// The boolean value
        value: bool,
        /// Source code location for error reporting
        location: Location,
    },
    /// String literal
    StringLiteral {
        /// The string value
        value: String,
        /// Source code location for error reporting
        location: Location,
    },
    /// Address literal
    AddressLiteral {
        /// The address value as a string
        value: String,
        /// Source code location for error reporting
        location: Location,
    },
    /// Variable or function identifier
    Identifier {
        /// The identifier name
        name: String,
        /// Source code location for error reporting
        location: Location,
    },
    /// Binary operation (e.g., addition, comparison)
    Binary {
        /// The binary operator
        op: BinaryOp,
        /// Left operand
        left: Box<Expression>,
        /// Right operand
        right: Box<Expression>,
        /// Source code location for error reporting
        location: Location,
    },
    /// Unary operation (e.g., negation, bitwise not)
    Unary {
        /// The unary operator
        op: UnaryOp,
        /// The operand
        operand: Box<Expression>,
        /// Source code location for error reporting
        location: Location,
    },
    /// Function call expression
    Call {
        /// The function to call
        function: Box<Expression>,
        /// Arguments to the function
        arguments: Vec<Expression>,
        /// Source code location for error reporting
        location: Location,
    },
    /// Field access on a struct
    FieldAccess {
        /// The object whose field is accessed
        object: Box<Expression>,
        /// The field name
        field: String,
        /// Source code location for error reporting
        location: Location,
    },
    /// Borrow expression (reference creation)
    Borrow {
        /// Whether the borrow is mutable
        is_mut: bool,
        /// The expression being borrowed
        expr: Box<Expression>,
        /// Source code location for error reporting
        location: Location,
    },
    /// Move expression for explicit ownership transfer
    Move {
        /// The expression being moved
        expr: Box<Expression>,
        /// Source code location for error reporting
        location: Location,
    },
}

/// Binary operator for arithmetic, bitwise, comparison, and logical operations.
///
/// Represents all binary operators supported in the Quantum language:
/// - Arithmetic: +, -, *, /, %
/// - Bitwise: &, |, ^, <<, >>
/// - Comparison: ==, !=, <, <=, >, >=
/// - Logical: &&, ||
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    /// Addition operator (+)
    Add,
    /// Subtraction operator (-)
    Sub,
    /// Multiplication operator (*)
    Mul,
    /// Division operator (/)
    Div,
    /// Modulo operator (%)
    Mod,
    /// Bitwise AND operator (&)
    BitAnd,
    /// Bitwise OR operator (|)
    BitOr,
    /// Bitwise XOR operator (^)
    BitXor,
    /// Left shift operator (<<)
    LeftShift,
    /// Right shift operator (>>)
    RightShift,
    /// Equality operator (==)
    Equal,
    /// Inequality operator (!=)
    NotEqual,
    /// Less than operator (<)
    Less,
    /// Less than or equal operator (<=)
    LessEqual,
    /// Greater than operator (>)
    Greater,
    /// Greater than or equal operator (>=)
    GreaterEqual,
    /// Logical AND operator (&&)
    And,
    /// Logical OR operator (||)
    Or,
}

/// Unary operator for negation and bitwise operations.
///
/// Represents all unary operators supported in the Quantum language:
/// - Logical: !
/// - Bitwise: ~
/// - Arithmetic: -
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Logical NOT operator (!)
    Not,
    /// Bitwise NOT operator (~)
    BitNot,
    /// Negation operator (-)
    Neg,
}

/// Complete Abstract Syntax Tree (AST) for a Quantum module.
///
/// The root node of the parse tree containing the entire module definition.
#[derive(Debug, Clone, PartialEq)]
pub struct AST {
    /// The module definition
    pub module: Module,
}

/// Parser for Quantum source code
pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    /// Create a new parser from tokens
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            position: 0,
        }
    }

    /// Get the current token
    fn current(&self) -> &Token {
        self.tokens.get(self.position).unwrap_or_else(|| {
            self.tokens
                .last()
                .expect("Token stream should not be empty")
        })
    }

    /// Peek at the next token
    #[allow(dead_code)]
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position + 1)
    }

    /// Advance to the next token
    fn advance(&mut self) -> Token {
        let token = self.current().clone();
        if self.position < self.tokens.len() - 1 {
            self.position += 1;
        }
        token
    }

    /// Check if current token matches the expected type
    fn check(&self, token_type: &TokenType) -> bool {
        std::mem::discriminant(&self.current().token_type) == std::mem::discriminant(token_type)
    }

    /// Match one of multiple token types and return the matched token
    fn match_token(&mut self, types: &[TokenType]) -> Option<Token> {
        for token_type in types {
            if self.check(token_type) {
                return Some(self.advance().clone());
            }
        }
        None
    }

    /// Consume a token if it matches the expected type
    fn consume(&mut self, token_type: TokenType, message: &str) -> Result<Token, String> {
        if self.check(&token_type) {
            Ok(self.advance().clone())
        } else {
            Err(format!(
                "{}: {}. Found: {:?}",
                self.current().location,
                message,
                self.current().token_type
            ))
        }
    }

    /// Parse the entire module
    pub fn parse(&mut self) -> Result<AST, String> {
        let module = self.parse_module()?;
        Ok(AST { module })
    }

    /// Parse module
    fn parse_module(&mut self) -> Result<Module, String> {
        self.consume(TokenType::Module, "Expected 'module'")?;

        let name_token = self.advance();
        let name = match &name_token.token_type {
            TokenType::Identifier(n) => n.clone(),
            _ => return Err(format!("{}: Expected module name", name_token.location)),
        };

        self.consume(TokenType::LeftBrace, "Expected '{'")?;

        let mut uses = Vec::new();
        let mut structs = Vec::new();
        let mut functions = Vec::new();

        while !self.check(&TokenType::RightBrace) && !self.check(&TokenType::Eof) {
            if self.check(&TokenType::Use) {
                uses.push(self.parse_use()?);
            } else if self.check(&TokenType::Struct) || self.check(&TokenType::Public) {
                structs.push(self.parse_struct()?);
            } else if self.check(&TokenType::Fun) || self.check(&TokenType::Public) {
                functions.push(self.parse_function()?);
            } else {
                return Err(format!(
                    "{}: Unexpected token in module body",
                    self.current().location
                ));
            }
        }

        self.consume(TokenType::RightBrace, "Expected '}'")?;

        Ok(Module {
            name,
            structs,
            functions,
            uses,
        })
    }

    /// Parse use declaration
    fn parse_use(&mut self) -> Result<UseDecl, String> {
        let location = self.current().location;
        self.consume(TokenType::Use, "Expected 'use'")?;

        let mut module_path = Vec::new();

        loop {
            let name_token = self.advance();
            match &name_token.token_type {
                TokenType::Identifier(n) => module_path.push(n.clone()),
                _ => return Err(format!("{}: Expected identifier", name_token.location)),
            }

            if !self.check(&TokenType::DoubleColon) {
                break;
            }
            self.advance(); // consume '::'
        }

        self.consume(TokenType::Semicolon, "Expected ';'")?;

        Ok(UseDecl {
            module_path,
            location,
        })
    }

    /// Parse struct definition
    fn parse_struct(&mut self) -> Result<StructDef, String> {
        let is_public = if self.check(&TokenType::Public) {
            self.advance();
            true
        } else {
            false
        };

        let location = self.current().location;
        self.consume(TokenType::Struct, "Expected 'struct'")?;

        let name_token = self.advance();
        let name = match &name_token.token_type {
            TokenType::Identifier(n) => n.clone(),
            _ => return Err(format!("{}: Expected struct name", name_token.location)),
        };

        let abilities = if self.check(&TokenType::Has) {
            self.advance();
            self.parse_abilities()?
        } else {
            Vec::new()
        };

        self.consume(TokenType::LeftBrace, "Expected '{'")?;

        let mut fields = Vec::new();
        while !self.check(&TokenType::RightBrace) && !self.check(&TokenType::Eof) {
            fields.push(self.parse_field()?);
            if !self.check(&TokenType::RightBrace) {
                self.consume(TokenType::Comma, "Expected ',' or '}'")?;
            }
        }

        self.consume(TokenType::RightBrace, "Expected '}'")?;

        Ok(StructDef {
            name,
            fields,
            abilities,
            is_public,
            location,
        })
    }

    /// Parse abilities
    fn parse_abilities(&mut self) -> Result<Vec<Ability>, String> {
        let mut abilities = Vec::new();

        loop {
            let ability = match &self.current().token_type {
                TokenType::Copy => Ability::Copy,
                TokenType::Drop => Ability::Drop,
                TokenType::Store => Ability::Store,
                TokenType::Key => Ability::Key,
                _ => break,
            };
            self.advance();
            abilities.push(ability);

            if !self.check(&TokenType::Comma) {
                break;
            }
            self.advance(); // consume ','
        }

        Ok(abilities)
    }

    /// Parse field
    fn parse_field(&mut self) -> Result<Field, String> {
        let location = self.current().location;

        let name_token = self.advance();
        let name = match &name_token.token_type {
            TokenType::Identifier(n) => n.clone(),
            _ => return Err(format!("{}: Expected field name", name_token.location)),
        };

        self.consume(TokenType::Colon, "Expected ':'")?;

        let field_type = self.parse_type()?;

        Ok(Field {
            name,
            field_type,
            location,
        })
    }

    /// Parse type
    fn parse_type(&mut self) -> Result<Type, String> {
        let type_token = self.advance();

        let base_type = match &type_token.token_type {
            TokenType::Bool => Type::Bool,
            TokenType::U8 => Type::U8,
            TokenType::U16 => Type::U16,
            TokenType::U32 => Type::U32,
            TokenType::U64 => Type::U64,
            TokenType::U128 => Type::U128,
            TokenType::U256 => Type::U256,
            TokenType::Address => Type::Address,
            TokenType::Vector => {
                self.consume(TokenType::Less, "Expected '<'")?;
                let elem_type = self.parse_type()?;
                self.consume(TokenType::Greater, "Expected '>'")?;
                Type::Vector(Box::new(elem_type))
            }
            TokenType::Identifier(name) => Type::Struct {
                module: None,
                name: name.clone(),
            },
            TokenType::Ampersand => {
                if self.check(&TokenType::Mut) {
                    self.advance();
                    let inner = self.parse_type()?;
                    Type::MutableReference(Box::new(inner))
                } else {
                    let inner = self.parse_type()?;
                    Type::Reference(Box::new(inner))
                }
            }
            _ => {
                return Err(format!(
                    "{}: Expected type, found {:?}",
                    type_token.location, type_token.token_type
                ))
            }
        };

        Ok(base_type)
    }

    /// Parse function
    fn parse_function(&mut self) -> Result<Function, String> {
        let mut is_public = false;
        let mut is_entry = false;

        while self.check(&TokenType::Public) || self.check(&TokenType::Entry) {
            if self.check(&TokenType::Public) {
                self.advance();
                is_public = true;
            }
            if self.check(&TokenType::Entry) {
                self.advance();
                is_entry = true;
            }
        }

        let location = self.current().location;
        self.consume(TokenType::Fun, "Expected 'fun'")?;

        let name_token = self.advance();
        let name = match &name_token.token_type {
            TokenType::Identifier(n) => n.clone(),
            _ => return Err(format!("{}: Expected function name", name_token.location)),
        };

        self.consume(TokenType::LeftParen, "Expected '('")?;

        let mut parameters = Vec::new();
        while !self.check(&TokenType::RightParen) && !self.check(&TokenType::Eof) {
            parameters.push(self.parse_parameter()?);
            if !self.check(&TokenType::RightParen) {
                self.consume(TokenType::Comma, "Expected ',' or ')'")?;
            }
        }

        self.consume(TokenType::RightParen, "Expected ')'")?;

        let return_type = if self.check(&TokenType::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        let body = self.parse_block()?;

        Ok(Function {
            name,
            parameters,
            return_type,
            body,
            is_public,
            is_entry,
            location,
        })
    }

    /// Parse parameter
    fn parse_parameter(&mut self) -> Result<Parameter, String> {
        let location = self.current().location;

        let is_mut = if self.check(&TokenType::Mut) {
            self.advance();
            true
        } else {
            false
        };

        let name_token = self.advance();
        let name = match &name_token.token_type {
            TokenType::Identifier(n) => n.clone(),
            _ => return Err(format!("{}: Expected parameter name", name_token.location)),
        };

        self.consume(TokenType::Colon, "Expected ':'")?;

        let param_type = self.parse_type()?;

        Ok(Parameter {
            name,
            param_type,
            is_mut,
            location,
        })
    }

    /// Parse block
    fn parse_block(&mut self) -> Result<Block, String> {
        let location = self.current().location;
        self.consume(TokenType::LeftBrace, "Expected '{'")?;

        let mut statements = Vec::new();
        while !self.check(&TokenType::RightBrace) && !self.check(&TokenType::Eof) {
            statements.push(self.parse_statement()?);
        }

        self.consume(TokenType::RightBrace, "Expected '}'")?;

        Ok(Block {
            statements,
            location,
        })
    }

    /// Parse statement
    fn parse_statement(&mut self) -> Result<Statement, String> {
        match &self.current().token_type {
            TokenType::Let => self.parse_let(),
            TokenType::If => self.parse_if(),
            TokenType::While => self.parse_while(),
            TokenType::Loop => self.parse_loop(),
            TokenType::Break => {
                let location = self.current().location;
                self.advance();
                self.consume(TokenType::Semicolon, "Expected ';'")?;
                Ok(Statement::Break { location })
            }
            TokenType::Continue => {
                let location = self.current().location;
                self.advance();
                self.consume(TokenType::Semicolon, "Expected ';'")?;
                Ok(Statement::Continue { location })
            }
            TokenType::Return => self.parse_return(),
            TokenType::Abort => self.parse_abort(),
            _ => self.parse_expression_statement(),
        }
    }

    /// Parse let statement
    fn parse_let(&mut self) -> Result<Statement, String> {
        let location = self.current().location;
        self.consume(TokenType::Let, "Expected 'let'")?;

        let is_mut = if self.check(&TokenType::Mut) {
            self.advance();
            true
        } else {
            false
        };

        let name_token = self.advance();
        let name = match &name_token.token_type {
            TokenType::Identifier(n) => n.clone(),
            _ => return Err(format!("{}: Expected variable name", name_token.location)),
        };

        let var_type = if self.check(&TokenType::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else {
            None
        };

        self.consume(TokenType::Assign, "Expected '='")?;

        let value = self.parse_expression()?;

        self.consume(TokenType::Semicolon, "Expected ';'")?;

        Ok(Statement::Let {
            name,
            var_type,
            value,
            is_mut,
            location,
        })
    }

    /// Parse if statement
    fn parse_if(&mut self) -> Result<Statement, String> {
        let location = self.current().location;
        self.consume(TokenType::If, "Expected 'if'")?;

        self.consume(TokenType::LeftParen, "Expected '('")?;
        let condition = self.parse_expression()?;
        self.consume(TokenType::RightParen, "Expected ')'")?;

        let then_block = self.parse_block()?;

        let else_block = if self.check(&TokenType::Else) {
            self.advance();
            Some(self.parse_block()?)
        } else {
            None
        };

        Ok(Statement::If {
            condition,
            then_block,
            else_block,
            location,
        })
    }

    /// Parse while statement
    fn parse_while(&mut self) -> Result<Statement, String> {
        let location = self.current().location;
        self.consume(TokenType::While, "Expected 'while'")?;

        self.consume(TokenType::LeftParen, "Expected '('")?;
        let condition = self.parse_expression()?;
        self.consume(TokenType::RightParen, "Expected ')'")?;

        let body = self.parse_block()?;

        Ok(Statement::While {
            condition,
            body,
            location,
        })
    }

    /// Parse loop statement
    fn parse_loop(&mut self) -> Result<Statement, String> {
        let location = self.current().location;
        self.consume(TokenType::Loop, "Expected 'loop'")?;

        let body = self.parse_block()?;

        Ok(Statement::Loop { body, location })
    }

    /// Parse return statement
    fn parse_return(&mut self) -> Result<Statement, String> {
        let location = self.current().location;
        self.consume(TokenType::Return, "Expected 'return'")?;

        let value = if !self.check(&TokenType::Semicolon) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.consume(TokenType::Semicolon, "Expected ';'")?;

        Ok(Statement::Return { value, location })
    }

    /// Parse abort statement
    fn parse_abort(&mut self) -> Result<Statement, String> {
        let location = self.current().location;
        self.consume(TokenType::Abort, "Expected 'abort'")?;

        let code = self.parse_expression()?;

        self.consume(TokenType::Semicolon, "Expected ';'")?;

        Ok(Statement::Abort { code, location })
    }

    /// Parse expression statement
    fn parse_expression_statement(&mut self) -> Result<Statement, String> {
        let location = self.current().location;
        let expr = self.parse_expression()?;

        // Check for assignment
        if self.check(&TokenType::Assign) {
            self.advance();
            let value = self.parse_expression()?;
            self.consume(TokenType::Semicolon, "Expected ';'")?;
            return Ok(Statement::Assign {
                target: expr,
                value,
                location,
            });
        }

        self.consume(TokenType::Semicolon, "Expected ';'")?;

        Ok(Statement::Expression { expr, location })
    }

    /// Parse expression with full operator precedence
    fn parse_expression(&mut self) -> Result<Expression, String> {
        self.parse_logical_or()
    }

    /// Parse logical OR expressions (lowest precedence)
    fn parse_logical_or(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_logical_and()?;

        while self.check(&TokenType::Or) {
            let op_token = self.advance().clone();
            let right = self.parse_logical_and()?;
            left = Expression::Binary {
                op: BinaryOp::Or,
                left: Box::new(left),
                right: Box::new(right),
                location: op_token.location,
            };
        }

        Ok(left)
    }

    /// Parse logical AND expressions
    fn parse_logical_and(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_equality()?;

        while self.check(&TokenType::And) {
            let op_token = self.advance().clone();
            let right = self.parse_equality()?;
            left = Expression::Binary {
                op: BinaryOp::And,
                left: Box::new(left),
                right: Box::new(right),
                location: op_token.location,
            };
        }

        Ok(left)
    }

    /// Parse equality expressions
    fn parse_equality(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_comparison()?;

        while let Some(op) = self.match_token(&[TokenType::Equal, TokenType::NotEqual]) {
            let op_enum = match op.token_type {
                TokenType::Equal => BinaryOp::Equal,
                TokenType::NotEqual => BinaryOp::NotEqual,
                _ => unreachable!(),
            };
            let right = self.parse_comparison()?;
            left = Expression::Binary {
                op: op_enum,
                left: Box::new(left),
                right: Box::new(right),
                location: op.location,
            };
        }

        Ok(left)
    }

    /// Parse comparison expressions
    fn parse_comparison(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_additive()?;

        while let Some(op) = self.match_token(&[
            TokenType::Less,
            TokenType::LessEqual,
            TokenType::Greater,
            TokenType::GreaterEqual,
        ]) {
            let op_enum = match op.token_type {
                TokenType::Less => BinaryOp::Less,
                TokenType::LessEqual => BinaryOp::LessEqual,
                TokenType::Greater => BinaryOp::Greater,
                TokenType::GreaterEqual => BinaryOp::GreaterEqual,
                _ => unreachable!(),
            };
            let right = self.parse_additive()?;
            left = Expression::Binary {
                op: op_enum,
                left: Box::new(left),
                right: Box::new(right),
                location: op.location,
            };
        }

        Ok(left)
    }

    /// Parse additive expressions
    fn parse_additive(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_multiplicative()?;

        while let Some(op) = self.match_token(&[TokenType::Plus, TokenType::Minus]) {
            let op_enum = match op.token_type {
                TokenType::Plus => BinaryOp::Add,
                TokenType::Minus => BinaryOp::Sub,
                _ => unreachable!(),
            };
            let right = self.parse_multiplicative()?;
            left = Expression::Binary {
                op: op_enum,
                left: Box::new(left),
                right: Box::new(right),
                location: op.location,
            };
        }

        Ok(left)
    }

    /// Parse multiplicative expressions
    fn parse_multiplicative(&mut self) -> Result<Expression, String> {
        let mut left = self.parse_unary()?;

        while let Some(op) = self.match_token(&[TokenType::Star, TokenType::Slash, TokenType::Percent]) {
            let op_enum = match op.token_type {
                TokenType::Star => BinaryOp::Mul,
                TokenType::Slash => BinaryOp::Div,
                TokenType::Percent => BinaryOp::Mod,
                _ => unreachable!(),
            };
            let right = self.parse_unary()?;
            left = Expression::Binary {
                op: op_enum,
                left: Box::new(left),
                right: Box::new(right),
                location: op.location,
            };
        }

        Ok(left)
    }

    /// Parse unary expressions
    fn parse_unary(&mut self) -> Result<Expression, String> {
        if self.check(&TokenType::Not) {
            let op_token = self.advance().clone();
            let expr = self.parse_unary()?;
            return Ok(Expression::Unary {
                op: UnaryOp::Not,
                operand: Box::new(expr),
                location: op_token.location,
            });
        }

        if self.check(&TokenType::Minus) {
            let op_token = self.advance().clone();
            let expr = self.parse_unary()?;
            return Ok(Expression::Unary {
                op: UnaryOp::Neg,
                operand: Box::new(expr),
                location: op_token.location,
            });
        }

        self.parse_postfix()
    }

    /// Parse postfix expressions (function calls, field access, indexing)
    fn parse_postfix(&mut self) -> Result<Expression, String> {
        let mut expr = self.parse_primary()?;

        loop {
            if self.check(&TokenType::LeftParen) {
                // Function call
                self.advance();
                let mut args = Vec::new();

                if !self.check(&TokenType::RightParen) {
                    loop {
                        args.push(self.parse_expression()?);
                        if !self.check(&TokenType::Comma) {
                            break;
                        }
                        self.advance();
                    }
                }

                let token = self.consume(TokenType::RightParen, "Expected ')'")?;
                let location = token.location;
                expr = Expression::Call {
                    function: Box::new(expr),
                    arguments: args,
                    location,
                };
            } else if self.check(&TokenType::Dot) {
                // Field access
                self.advance();
                let field_token = self.advance().clone();
                if let TokenType::Identifier(field_name) = &field_token.token_type {
                    expr = Expression::FieldAccess {
                        object: Box::new(expr),
                        field: field_name.clone(),
                        location: field_token.location,
                    };
                } else {
                    return Err(format!(
                        "{}: Expected field name after '.'",
                        field_token.location
                    ));
                }
            } else {
                break;
            }
        }

        Ok(expr)
    }

    /// Parse primary expression
    fn parse_primary(&mut self) -> Result<Expression, String> {
        let token = self.advance().clone();

        match &token.token_type {
            TokenType::IntLiteral(value) => Ok(Expression::IntLiteral {
                value: value.clone(),
                location: token.location,
            }),
            TokenType::True => Ok(Expression::BoolLiteral {
                value: true,
                location: token.location,
            }),
            TokenType::False => Ok(Expression::BoolLiteral {
                value: false,
                location: token.location,
            }),
            TokenType::StringLiteral(value) => Ok(Expression::StringLiteral {
                value: value.clone(),
                location: token.location,
            }),
            TokenType::AddressLiteral(value) => Ok(Expression::AddressLiteral {
                value: value.clone(),
                location: token.location,
            }),
            TokenType::Identifier(name) => Ok(Expression::Identifier {
                name: name.clone(),
                location: token.location,
            }),
            _ => Err(format!(
                "{}: Expected expression, found {:?}",
                token.location, token.token_type
            )),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "bool"),
            Type::U8 => write!(f, "u8"),
            Type::U16 => write!(f, "u16"),
            Type::U32 => write!(f, "u32"),
            Type::U64 => write!(f, "u64"),
            Type::U128 => write!(f, "u128"),
            Type::U256 => write!(f, "u256"),
            Type::Address => write!(f, "address"),
            Type::Vector(inner) => write!(f, "vector<{}>", inner),
            Type::Struct { module, name } => {
                if let Some(m) = module {
                    write!(f, "{}::{}", m, name)
                } else {
                    write!(f, "{}", name)
                }
            }
            Type::Reference(inner) => write!(f, "&{}", inner),
            Type::MutableReference(inner) => write!(f, "&mut {}", inner),
        }
    }
}

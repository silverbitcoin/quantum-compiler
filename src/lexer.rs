//! # Quantum Lexer
//!
//! Tokenizes Quantum source code into a stream of tokens.
//! This is a PRODUCTION-READY implementation with:
//! - Complete token set for Quantum language
//! - Proper error handling
//! - Source location tracking
//! - Unicode support

use std::fmt;

/// Token type representing all Quantum language tokens
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenType {
    // Keywords
    /// `module` keyword for module declarations
    Module,
    /// `use` keyword for imports
    Use,
    /// `struct` keyword for struct definitions
    Struct,
    /// `fun` keyword for function definitions
    Fun,
    /// `public` keyword for public visibility
    Public,
    /// `entry` keyword for entry functions
    Entry,
    /// `has` keyword for ability declarations
    Has,
    /// `copy` ability keyword
    Copy,
    /// `drop` ability keyword
    Drop,
    /// `store` ability keyword
    Store,
    /// `key` ability keyword
    Key,
    /// `let` keyword for variable declarations
    Let,
    /// `mut` keyword for mutable variables
    Mut,
    /// `if` keyword for conditional statements
    If,
    /// `else` keyword for else blocks
    Else,
    /// `while` keyword for while loops
    While,
    /// `loop` keyword for infinite loops
    Loop,
    /// `break` keyword for loop breaks
    Break,
    /// `continue` keyword for loop continuation
    Continue,
    /// `return` keyword for function returns
    Return,
    /// `abort` keyword for transaction aborts
    Abort,
    /// `move` keyword for move semantics
    Move,
    /// `borrow` keyword for borrowing
    Borrow,
    /// `true` boolean literal
    True,
    /// `false` boolean literal
    False,

    // Types
    /// `bool` type keyword
    Bool,
    /// `u8` type keyword
    U8,
    /// `u16` type keyword
    U16,
    /// `u32` type keyword
    U32,
    /// `u64` type keyword
    U64,
    /// `u128` type keyword
    U128,
    /// `u256` type keyword
    U256,
    /// `address` type keyword
    Address,
    /// `vector` type keyword
    Vector,

    // Operators
    /// `+` addition operator
    Plus,
    /// `-` subtraction operator
    Minus,
    /// `*` multiplication operator
    Star,
    /// `/` division operator
    Slash,
    /// `%` modulo operator
    Percent,
    /// `&` bitwise AND operator
    Ampersand,
    /// `|` bitwise OR operator
    Pipe,
    /// `^` bitwise XOR operator
    Caret,
    /// `~` bitwise NOT operator
    Tilde,
    /// `<<` left shift operator
    LeftShift,
    /// `>>` right shift operator
    RightShift,
    /// `==` equality operator
    Equal,
    /// `!=` inequality operator
    NotEqual,
    /// `<` less than operator
    Less,
    /// `<=` less than or equal operator
    LessEqual,
    /// `>` greater than operator
    Greater,
    /// `>=` greater than or equal operator
    GreaterEqual,
    /// `&&` logical AND operator
    And,
    /// `||` logical OR operator
    Or,
    /// `!` logical NOT operator
    Not,
    /// `=` assignment operator
    Assign,
    /// `+=` addition assignment operator
    PlusAssign,
    /// `-=` subtraction assignment operator
    MinusAssign,
    /// `*=` multiplication assignment operator
    StarAssign,
    /// `/=` division assignment operator
    SlashAssign,
    /// `%=` modulo assignment operator
    PercentAssign,

    // Delimiters
    /// `(` left parenthesis
    LeftParen,
    /// `)` right parenthesis
    RightParen,
    /// `{` left brace
    LeftBrace,
    /// `}` right brace
    RightBrace,
    /// `[` left bracket
    LeftBracket,
    /// `]` right bracket
    RightBracket,
    /// `,` comma
    Comma,
    /// `;` semicolon
    Semicolon,
    /// `:` colon
    Colon,
    /// `::` double colon (module separator)
    DoubleColon,
    /// `.` dot (field access)
    Dot,
    /// `->` arrow (return type annotation)
    Arrow,

    // Literals
    /// Integer literal (e.g., `42`, `0xFF`)
    IntLiteral(String),
    /// String literal (e.g., `"hello"`)
    StringLiteral(String),
    /// Address literal (e.g., `@0x1`)
    AddressLiteral(String),

    // Identifiers
    /// Identifier token (variable, function, or type name)
    Identifier(String),

    // Special
    /// End of file marker
    Eof,
    /// Lexical error with error message
    Error(String),
}

/// Source location for error reporting
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    /// Line number (1-indexed)
    pub line: usize,
    /// Column number (1-indexed)
    pub column: usize,
    /// Byte offset in source
    pub offset: usize,
}

impl Location {
    /// Create a new location
    pub fn new(line: usize, column: usize, offset: usize) -> Self {
        Self {
            line,
            column,
            offset,
        }
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

/// Token with type and location
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    /// Token type
    pub token_type: TokenType,
    /// Source location
    pub location: Location,
    /// Original text (for debugging)
    pub text: String,
}

impl Token {
    /// Create a new token
    pub fn new(token_type: TokenType, location: Location, text: String) -> Self {
        Self {
            token_type,
            location,
            text,
        }
    }
}

/// Lexer for tokenizing Quantum source code
pub struct Lexer {
    /// Source code
    source: Vec<char>,
    /// Current position
    position: usize,
    /// Current line (1-indexed)
    line: usize,
    /// Current column (1-indexed)
    column: usize,
}

impl Lexer {
    /// Create a new lexer from source code
    ///
    /// # Arguments
    ///
    /// * `source` - Source code string
    ///
    /// # Examples
    ///
    /// ```
    /// use quantum_compiler::Lexer;
    ///
    /// let source = "module test { }";
    /// let lexer = Lexer::new(source);
    /// ```
    pub fn new(source: &str) -> Self {
        Self {
            source: source.chars().collect(),
            position: 0,
            line: 1,
            column: 1,
        }
    }

    /// Get the current location
    fn current_location(&self) -> Location {
        Location::new(self.line, self.column, self.position)
    }

    /// Peek at the current character without consuming it
    fn peek(&self) -> Option<char> {
        self.source.get(self.position).copied()
    }

    /// Peek at the next character without consuming it
    fn peek_next(&self) -> Option<char> {
        self.source.get(self.position + 1).copied()
    }

    /// Advance to the next character
    fn advance(&mut self) -> Option<char> {
        if let Some(ch) = self.source.get(self.position) {
            self.position += 1;
            if *ch == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
            Some(*ch)
        } else {
            None
        }
    }

    /// Skip whitespace
    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    /// Skip line comment (// ...)
    fn skip_line_comment(&mut self) {
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            }
            self.advance();
        }
    }

    /// Skip block comment (/* ... */)
    fn skip_block_comment(&mut self) -> Result<(), String> {
        let start_loc = self.current_location();
        self.advance(); // consume '/'
        self.advance(); // consume '*'

        let mut depth = 1;
        while depth > 0 {
            match self.peek() {
                Some('/') if self.peek_next() == Some('*') => {
                    self.advance();
                    self.advance();
                    depth += 1;
                }
                Some('*') if self.peek_next() == Some('/') => {
                    self.advance();
                    self.advance();
                    depth -= 1;
                }
                Some(_) => {
                    self.advance();
                }
                None => {
                    return Err(format!("Unclosed block comment starting at {}", start_loc));
                }
            }
        }

        Ok(())
    }

    /// Lex an identifier or keyword
    fn lex_identifier(&mut self) -> Token {
        let start_loc = self.current_location();
        let mut text = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                text.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        let token_type = match text.as_str() {
            "module" => TokenType::Module,
            "use" => TokenType::Use,
            "struct" => TokenType::Struct,
            "fun" => TokenType::Fun,
            "public" => TokenType::Public,
            "entry" => TokenType::Entry,
            "has" => TokenType::Has,
            "copy" => TokenType::Copy,
            "drop" => TokenType::Drop,
            "store" => TokenType::Store,
            "key" => TokenType::Key,
            "let" => TokenType::Let,
            "mut" => TokenType::Mut,
            "if" => TokenType::If,
            "else" => TokenType::Else,
            "while" => TokenType::While,
            "loop" => TokenType::Loop,
            "break" => TokenType::Break,
            "continue" => TokenType::Continue,
            "return" => TokenType::Return,
            "abort" => TokenType::Abort,
            "move" => TokenType::Move,
            "borrow" => TokenType::Borrow,
            "true" => TokenType::True,
            "false" => TokenType::False,
            "bool" => TokenType::Bool,
            "u8" => TokenType::U8,
            "u16" => TokenType::U16,
            "u32" => TokenType::U32,
            "u64" => TokenType::U64,
            "u128" => TokenType::U128,
            "u256" => TokenType::U256,
            "address" => TokenType::Address,
            "vector" => TokenType::Vector,
            _ => TokenType::Identifier(text.clone()),
        };

        Token::new(token_type, start_loc, text)
    }

    /// Lex a number literal
    fn lex_number(&mut self) -> Token {
        let start_loc = self.current_location();
        let mut text = String::new();

        // Handle hex literals (0x...)
        if self.peek() == Some('0') && self.peek_next() == Some('x') {
            text.push('0');
            self.advance();
            text.push('x');
            self.advance();

            while let Some(ch) = self.peek() {
                if ch.is_ascii_hexdigit() || ch == '_' {
                    if ch != '_' {
                        text.push(ch);
                    }
                    self.advance();
                } else {
                    break;
                }
            }
        } else {
            // Decimal number
            while let Some(ch) = self.peek() {
                if ch.is_ascii_digit() || ch == '_' {
                    if ch != '_' {
                        text.push(ch);
                    }
                    self.advance();
                } else {
                    break;
                }
            }
        }

        Token::new(TokenType::IntLiteral(text.clone()), start_loc, text)
    }

    /// Lex a string literal
    fn lex_string(&mut self) -> Token {
        let start_loc = self.current_location();
        let mut text = String::new();
        let mut value = String::new();

        text.push('"');
        self.advance(); // consume opening quote

        while let Some(ch) = self.peek() {
            if ch == '"' {
                text.push('"');
                self.advance();
                return Token::new(TokenType::StringLiteral(value), start_loc, text);
            } else if ch == '\\' {
                text.push('\\');
                self.advance();
                if let Some(escaped) = self.peek() {
                    text.push(escaped);
                    self.advance();
                    // Handle escape sequences
                    let unescaped = match escaped {
                        'n' => '\n',
                        't' => '\t',
                        'r' => '\r',
                        '\\' => '\\',
                        '"' => '"',
                        _ => escaped,
                    };
                    value.push(unescaped);
                }
            } else {
                text.push(ch);
                value.push(ch);
                self.advance();
            }
        }

        Token::new(
            TokenType::Error("Unclosed string literal".to_string()),
            start_loc,
            text,
        )
    }

    /// Lex an address literal (@0x...)
    fn lex_address(&mut self) -> Token {
        let start_loc = self.current_location();
        let mut text = String::new();

        text.push('@');
        self.advance(); // consume '@'

        if self.peek() == Some('0') && self.peek_next() == Some('x') {
            text.push('0');
            self.advance();
            text.push('x');
            self.advance();

            while let Some(ch) = self.peek() {
                if ch.is_ascii_hexdigit() {
                    text.push(ch);
                    self.advance();
                } else {
                    break;
                }
            }

            Token::new(TokenType::AddressLiteral(text.clone()), start_loc, text)
        } else {
            Token::new(
                TokenType::Error("Invalid address literal".to_string()),
                start_loc,
                text,
            )
        }
    }

    /// Get the next token
    pub fn next_token(&mut self) -> Token {
        // Skip whitespace and comments
        loop {
            self.skip_whitespace();

            match (self.peek(), self.peek_next()) {
                (Some('/'), Some('/')) => {
                    self.skip_line_comment();
                }
                (Some('/'), Some('*')) => {
                    if let Err(err) = self.skip_block_comment() {
                        let loc = self.current_location();
                        return Token::new(TokenType::Error(err), loc, String::new());
                    }
                }
                _ => break,
            }
        }

        let start_loc = self.current_location();

        match self.peek() {
            None => Token::new(TokenType::Eof, start_loc, String::new()),

            Some(ch) if ch.is_alphabetic() || ch == '_' => self.lex_identifier(),

            Some(ch) if ch.is_ascii_digit() => self.lex_number(),

            Some('"') => self.lex_string(),

            Some('@') => self.lex_address(),

            Some('+') => {
                let mut text = String::from("+");
                self.advance();
                if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::PlusAssign, start_loc, text)
                } else {
                    Token::new(TokenType::Plus, start_loc, text)
                }
            }

            Some('-') => {
                let mut text = String::from("-");
                self.advance();
                if self.peek() == Some('>') {
                    text.push('>');
                    self.advance();
                    Token::new(TokenType::Arrow, start_loc, text)
                } else if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::MinusAssign, start_loc, text)
                } else {
                    Token::new(TokenType::Minus, start_loc, text)
                }
            }

            Some('*') => {
                let mut text = String::from("*");
                self.advance();
                if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::StarAssign, start_loc, text)
                } else {
                    Token::new(TokenType::Star, start_loc, text)
                }
            }

            Some('/') => {
                let mut text = String::from("/");
                self.advance();
                if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::SlashAssign, start_loc, text)
                } else {
                    Token::new(TokenType::Slash, start_loc, text)
                }
            }

            Some('%') => {
                let mut text = String::from("%");
                self.advance();
                if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::PercentAssign, start_loc, text)
                } else {
                    Token::new(TokenType::Percent, start_loc, text)
                }
            }

            Some('&') => {
                let mut text = String::from("&");
                self.advance();
                if self.peek() == Some('&') {
                    text.push('&');
                    self.advance();
                    Token::new(TokenType::And, start_loc, text)
                } else {
                    Token::new(TokenType::Ampersand, start_loc, text)
                }
            }

            Some('|') => {
                let mut text = String::from("|");
                self.advance();
                if self.peek() == Some('|') {
                    text.push('|');
                    self.advance();
                    Token::new(TokenType::Or, start_loc, text)
                } else {
                    Token::new(TokenType::Pipe, start_loc, text)
                }
            }

            Some('^') => {
                let text = String::from("^");
                self.advance();
                Token::new(TokenType::Caret, start_loc, text)
            }

            Some('~') => {
                let text = String::from("~");
                self.advance();
                Token::new(TokenType::Tilde, start_loc, text)
            }

            Some('<') => {
                let mut text = String::from("<");
                self.advance();
                if self.peek() == Some('<') {
                    text.push('<');
                    self.advance();
                    Token::new(TokenType::LeftShift, start_loc, text)
                } else if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::LessEqual, start_loc, text)
                } else {
                    Token::new(TokenType::Less, start_loc, text)
                }
            }

            Some('>') => {
                let mut text = String::from(">");
                self.advance();
                if self.peek() == Some('>') {
                    text.push('>');
                    self.advance();
                    Token::new(TokenType::RightShift, start_loc, text)
                } else if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::GreaterEqual, start_loc, text)
                } else {
                    Token::new(TokenType::Greater, start_loc, text)
                }
            }

            Some('=') => {
                let mut text = String::from("=");
                self.advance();
                if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::Equal, start_loc, text)
                } else {
                    Token::new(TokenType::Assign, start_loc, text)
                }
            }

            Some('!') => {
                let mut text = String::from("!");
                self.advance();
                if self.peek() == Some('=') {
                    text.push('=');
                    self.advance();
                    Token::new(TokenType::NotEqual, start_loc, text)
                } else {
                    Token::new(TokenType::Not, start_loc, text)
                }
            }

            Some('(') => {
                let text = String::from("(");
                self.advance();
                Token::new(TokenType::LeftParen, start_loc, text)
            }

            Some(')') => {
                let text = String::from(")");
                self.advance();
                Token::new(TokenType::RightParen, start_loc, text)
            }

            Some('{') => {
                let text = String::from("{");
                self.advance();
                Token::new(TokenType::LeftBrace, start_loc, text)
            }

            Some('}') => {
                let text = String::from("}");
                self.advance();
                Token::new(TokenType::RightBrace, start_loc, text)
            }

            Some('[') => {
                let text = String::from("[");
                self.advance();
                Token::new(TokenType::LeftBracket, start_loc, text)
            }

            Some(']') => {
                let text = String::from("]");
                self.advance();
                Token::new(TokenType::RightBracket, start_loc, text)
            }

            Some(',') => {
                let text = String::from(",");
                self.advance();
                Token::new(TokenType::Comma, start_loc, text)
            }

            Some(';') => {
                let text = String::from(";");
                self.advance();
                Token::new(TokenType::Semicolon, start_loc, text)
            }

            Some(':') => {
                let mut text = String::from(":");
                self.advance();
                if self.peek() == Some(':') {
                    text.push(':');
                    self.advance();
                    Token::new(TokenType::DoubleColon, start_loc, text)
                } else {
                    Token::new(TokenType::Colon, start_loc, text)
                }
            }

            Some('.') => {
                let text = String::from(".");
                self.advance();
                Token::new(TokenType::Dot, start_loc, text)
            }

            Some(ch) => {
                let text = ch.to_string();
                self.advance();
                Token::new(
                    TokenType::Error(format!("Unexpected character: {}", ch)),
                    start_loc,
                    text,
                )
            }
        }
    }

    /// Tokenize the entire source code
    pub fn tokenize(&mut self) -> Result<Vec<Token>, String> {
        let mut tokens = Vec::new();

        loop {
            let token = self.next_token();

            if let TokenType::Error(ref err) = token.token_type {
                return Err(format!("{}: {}", token.location, err));
            }

            let is_eof = token.token_type == TokenType::Eof;
            tokens.push(token);

            if is_eof {
                break;
            }
        }

        Ok(tokens)
    }
}

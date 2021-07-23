use std::collections::HashMap;

fn main() {
    let form1 = String::from("($lambda x:int.+:int$to int$to int x 1):int$to int");
    let form2 = String::from(
        "(($lambda f: int $to int. $lambda y: int. f(f y))($lambda z: int. + z 1:int)): int $to int",
    );
    let form3 = String::from("$lambda f: A $to B. $lambda g: B $to C. $lambda a: A. g (f a)");

    let invalid1 = String::from("+ x 10");
    let invalid2 = String::from("$lambda f: A $to B. $lambda g: B $to C. g f");

    compile(form1.as_str());
    println!("");
    compile(form2.as_str());
    println!("");
    compile(form3.as_str());
    println!("");
    compile(invalid1.as_str());
    println!("");
    compile(invalid2.as_str());
}

fn compile(code: &str) {
    println!("expr: {}", code);
    let mut lexer = Lexer::new(code);
    lexer.tokenize();
    let mut parser = Parser::new(lexer.tokens);
    let ast = parser.parse();
    match type_check(ast) {
        Ok(ty) => println!("OK!: {}", ty),
        Err(msg) => println!("Fail!: {}", msg),
    }
}

// == Type Checker ==

type TypeCheckError = String;
type TypeEnvironment = HashMap<String, TypeExpr>;

fn type_check(ast: AST) -> Result<TypeExpr, TypeCheckError> {
    let mut env = TypeEnvironment::new();
    env.insert(String::from("+"), TypeExpr::op_plus());
    rec_type_check(ast, env)
}

fn rec_type_check(ast: AST, env: TypeEnvironment) -> Result<TypeExpr, TypeCheckError> {
    let term_ty = ast.ty;
    match ast.kind {
        ASTKind::Apply(func_ast, arg_ast) => {
            let func_ty = rec_type_check(*func_ast, env.clone())?;
            let arg_ty = rec_type_check(*arg_ast, env)?;
            match func_ty {
                TypeExpr::Unknown => panic!("Unknown Type must not appear ! @ check Apply"),
                TypeExpr::SingleType(_) => panic!("Single Type cannot be applyed ! @ check Apply"),
                TypeExpr::FuncType(arg, ret_ty) => {
                    if *arg != arg_ty {
                        let msg = String::from("args type invalid @ check Apply");
                        Err(msg)
                    } else {
                        if term_ty != TypeExpr::Unknown {
                            if *ret_ty == term_ty {
                                Ok(*ret_ty)
                            } else {
                                let msg =
                                    String::from("Type annotation is invalid ! @ check Apply");
                                Err(msg)
                            }
                        } else {
                            Ok(*ret_ty)
                        }
                    }
                }
            }
        }
        ASTKind::Identifier(id) => match env.get(&id) {
            None => {
                let msg = format!("env has no information about `{}` @ check Identifier", id);
                Err(msg)
            }
            Some(val) => Ok(val.clone()),
        },
        ASTKind::LambdaFormula(arg_id, arg_ty, ret) => {
            let mut new_env = env.clone();
            new_env.insert(arg_id, arg_ty.clone());
            let ret_ty = rec_type_check(*ret, new_env)?;
            let func_ty = TypeExpr::FuncType(Box::new(arg_ty), Box::new(ret_ty));
            Ok(func_ty)
        }
        ASTKind::Number(_) => Ok(TypeExpr::int()),
    }
}

// == Parser ==

struct Parser {
    tokens: Vec<Token>,
    look: usize,
}

impl Parser {
    fn new(tokens: Vec<Token>) -> Self {
        Self { tokens, look: 0 }
    }

    fn parse(&mut self) -> AST {
        self.parse_apply()
    }

    fn parse_apply(&mut self) -> AST {
        // apply -> term [term]*
        let mut term = self.parse_term();
        while !self.at_end() {
            let token = self.look_at().unwrap();
            match token.kind {
                TokenKind::Symbol(sym_kind) => match sym_kind {
                    SymbolKind::RightBracket | SymbolKind::Colon => break,
                    _ => (),
                },
                _ => (),
            }
            let arg = self.parse_term();
            term = AST::new_apply_term(term, arg);
        }
        term
    }

    fn parse_term(&mut self) -> AST {
        // term -> [Number | Identifier | $lambda Identifier : type . apply | ( apply )] [: type]?
        let token = self.look_at().unwrap();
        let kind;
        let mut ty = TypeExpr::Unknown;
        match token.kind.clone() {
            TokenKind::Number(n) => {
                self.forward();
                kind = ASTKind::Number(n);
                ty = TypeExpr::int();
            }
            TokenKind::Identifier(id) => {
                self.forward();
                kind = ASTKind::Identifier(id);
            }
            TokenKind::Symbol(sym) => match sym {
                SymbolKind::Lambda => return self.parse_lambda(),
                SymbolKind::LeftBracket => {
                    // LeftBracket
                    self.forward();

                    // apply
                    let applyed = self.parse_apply();

                    // RightBracket
                    let token = self.look_at().unwrap();
                    match token.kind {
                        TokenKind::Symbol(sym) => match sym {
                            SymbolKind::RightBracket => (),
                            _ => panic!("invalid symbol ! expected: RightBracket @ parse_term"),
                        },
                        _ => panic!("invalid token ! expected: RightBracket @ parse_term"),
                    }
                    self.forward();

                    return applyed;
                }
                _ => panic!("invalid token ! @ parse_term"),
            },
        };
        if !self.at_end() {
            let token = self.look_at().unwrap();
            match token.kind {
                TokenKind::Symbol(sym) => match sym {
                    SymbolKind::Colon => {
                        // : type

                        // Colon
                        self.forward();

                        // type
                        ty = self.parse_type();
                    }
                    _ => (),
                },
                _ => (),
            }
        };
        AST { kind, ty }
    }

    fn parse_lambda(&mut self) -> AST {
        // lambda -> $lambda Identifier : type . apply

        // $lambda
        self.forward();

        // Identifier
        let token = self.look_at().unwrap();
        let id = match token.kind {
            TokenKind::Identifier(id) => id,
            _ => panic!("invalid token ! expected: Identifier @ parse_lambda"),
        };
        self.forward();

        // Colon
        let token = self.look_at().unwrap();
        match token.kind {
            TokenKind::Symbol(sym) => match sym {
                SymbolKind::Colon => (),
                _ => panic!("invalid symbol ! expected: Colon @ parse_lambda"),
            },
            _ => panic!("invalid token ! expected: Colon @ parse_lambda"),
        }
        self.forward();

        // type
        let type_term = self.parse_type();

        // Dot
        let token = self.look_at().unwrap();
        match token.kind {
            TokenKind::Symbol(sym) => match sym {
                SymbolKind::Dot => (),
                _ => panic!("invalid symbol ! expected: Dot @ parse_lambda"),
            },
            _ => panic!("invalid token ! expected: Dot @ parse_lambda"),
        }
        self.forward();

        // apply
        let applyed = self.parse_apply();

        let kind = ASTKind::LambdaFormula(id, type_term, Box::new(applyed));
        AST {
            kind,
            ty: TypeExpr::Unknown,
        }
    }

    fn parse_type(&mut self) -> TypeExpr {
        // type -> [Identifier | ( type )] [$to type]?
        let token = self.look_at().unwrap();
        let type_term = match token.kind {
            TokenKind::Identifier(id) => {
                let type_term = TypeExpr::SingleType(id);
                self.forward();
                type_term
            }
            TokenKind::Symbol(sym) => match sym {
                SymbolKind::LeftBracket => {
                    // ( type )

                    // LeftBracket
                    self.forward();

                    // type
                    let type_term = self.parse_type();

                    // RightBracket
                    let token = self.look_at().unwrap();
                    match token.kind {
                        TokenKind::Symbol(sym) => match sym {
                            SymbolKind::RightBracket => (),
                            _ => panic!("invalid symbol ! expected: RightBracket @ parse_type"),
                        },
                        _ => panic!("invalid token ! expected: RightBracket @ parse_type"),
                    }
                    self.forward();

                    type_term
                }
                _ => panic!("invalid symbol ! expected: LeftBracket @ parse_type"),
            },
            _ => panic!("invalid token ! @ parse_type"),
        };

        if !self.at_end() {
            let token = self.look_at().unwrap();
            match token.kind {
                TokenKind::Symbol(sym) => match sym {
                    SymbolKind::To => {
                        // $to type

                        // $to
                        self.forward();

                        // type
                        let to_type_term = self.parse_type();

                        TypeExpr::FuncType(Box::new(type_term), Box::new(to_type_term))
                    }
                    _ => type_term,
                },
                _ => type_term,
            }
        } else {
            type_term
        }
    }

    fn forward(&mut self) {
        self.look += 1;
    }

    fn at_end(&self) -> bool {
        self.look >= self.tokens.len()
    }

    fn look_at(&self) -> Option<Token> {
        self.tokens.get(self.look).map(|t| t.clone())
    }
}

/*
    apply -> term [term]*
    term -> [Number | Identifier | $lambda Identifier : type . apply | ( apply )] [: type]?
    type -> [Identifier | ( type )] [$to type]?
*/

#[derive(Debug, Clone, PartialEq)]
enum TypeExpr {
    SingleType(String),
    FuncType(Box<TypeExpr>, Box<TypeExpr>),
    Unknown,
}

impl TypeExpr {
    fn int() -> Self {
        TypeExpr::SingleType(String::from("int"))
    }

    fn op_plus() -> Self {
        let int2int = TypeExpr::FuncType(Box::new(Self::int()), Box::new(Self::int()));
        TypeExpr::FuncType(Box::new(Self::int()), Box::new(int2int))
    }
}

impl std::fmt::Display for TypeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TypeExpr::SingleType(ty) => write!(f, "{}", ty),
            TypeExpr::FuncType(ty1, ty2) => write!(f, "({} -> {})", ty1, ty2),
            TypeExpr::Unknown => write!(f, "'unknown"),
        }
    }
}

#[derive(Debug, Clone)]
enum ASTKind {
    Number(u32),
    Identifier(String),
    LambdaFormula(String, TypeExpr, Box<AST>),
    Apply(Box<AST>, Box<AST>),
}

#[derive(Debug, Clone)]
struct AST {
    kind: ASTKind,
    ty: TypeExpr,
}

impl AST {
    fn new_apply_term(func: AST, arg: AST) -> AST {
        let kind = ASTKind::Apply(Box::new(func), Box::new(arg));
        AST {
            kind,
            ty: TypeExpr::Unknown,
        }
    }
}

impl std::fmt::Display for AST {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.clone().kind {
            ASTKind::Number(n) => write!(f, "{}", n),
            ASTKind::Identifier(id) => write!(f, "{}", id),
            ASTKind::LambdaFormula(arg_id, arg_ty, ast) => {
                write!(f, "λ {}: {}. {}", arg_id, arg_ty, ast)
            }
            ASTKind::Apply(ast1, ast2) => write!(f, "({}) ({})", ast1, ast2),
        }
    }
}

// == Lexer ==

#[derive(Debug, Clone)]
struct Lexer {
    code: Vec<char>,
    look: usize,
    tokens: Vec<Token>,
}

impl Lexer {
    fn new(code: &str) -> Self {
        let code = code.chars().collect::<Vec<char>>();
        Self {
            code,
            look: 0,
            tokens: Vec::new(),
        }
    }

    fn tokenize(&mut self) {
        self.rec_tokenize();
    }

    fn rec_tokenize(&mut self) {
        if !self.at_end() {
            let looked = self.look_at().unwrap();
            if self.check_symbol(looked) {
                // symbol
                self.tokenize_symbol()
            } else if looked.is_ascii_digit() {
                // number
                self.tokenize_number();
            } else if looked.is_ascii_alphabetic() || looked == '+' {
                // Identifier
                self.tokenize_identifier();
            } else if looked.is_ascii_whitespace() {
                // whitespace
                self.forward();
            } else {
                panic!("Lexer looked invalid character: {}", looked);
            }
            self.rec_tokenize()
        }
    }

    fn tokenize_symbol(&mut self) {
        let c = self.look_at().unwrap();
        self.forward();
        let mut symbols = vec![c];
        // symbolの文字列を抽出
        if c == '$' {
            // '$' 以降に続いている ascii_alphabetic をまとめて抽出
            while !self.at_end() {
                let c = self.look_at().unwrap();
                if c.is_ascii_alphabetic() {
                    symbols.push(c);
                    self.forward();
                } else {
                    break;
                }
            }
        }
        let sym_str = symbols.iter().collect::<String>();
        let sym_kind = match sym_str.as_str() {
            "(" => SymbolKind::LeftBracket,
            ")" => SymbolKind::RightBracket,
            ":" => SymbolKind::Colon,
            "." => SymbolKind::Dot,
            "$to" => SymbolKind::To,
            "$lambda" => SymbolKind::Lambda,
            _ => panic!("Lexer discovered invalid symbol!"),
        };
        let kind = TokenKind::Symbol(sym_kind);
        let token = Token::new(kind);
        self.tokens.push(token);
    }

    fn tokenize_number(&mut self) {
        let mut nums = vec![];
        while !self.at_end() {
            let c = self.look_at().unwrap();
            if c.is_ascii_digit() {
                nums.push(c);
                self.forward();
            } else {
                break;
            }
        }
        let n = nums.iter().collect::<String>().parse::<u32>().unwrap();
        let kind = TokenKind::Number(n);
        let token = Token::new(kind);
        self.tokens.push(token);
    }

    fn tokenize_identifier(&mut self) {
        let mut words = vec![];
        while !self.at_end() {
            let c = self.look_at().unwrap();
            if c.is_ascii_alphabetic() {
                words.push(c);
                self.forward();
            } else if c == '+' {
                words.push(c);
                self.forward();
                break;
            } else {
                break;
            }
        }
        let id_name = words.iter().collect::<String>();
        let kind = TokenKind::Identifier(id_name);
        let token = Token::new(kind);
        self.tokens.push(token);
    }

    fn check_symbol(&self, looked: char) -> bool {
        match looked {
            '$' | ':' | '.' | '(' | ')' => true,
            _ => false,
        }
    }

    fn forward(&mut self) {
        self.look += 1;
    }

    fn at_end(&self) -> bool {
        self.look >= self.code.len()
    }

    fn look_at(&self) -> Option<char> {
        self.code.get(self.look).map(|&c| c)
    }
}

#[derive(Debug, Clone)]
struct Token {
    kind: TokenKind,
}

impl Token {
    fn new(kind: TokenKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum TokenKind {
    Symbol(SymbolKind),
    Identifier(String),
    Number(u32),
}

#[derive(Debug, Clone, PartialEq)]
enum SymbolKind {
    Lambda,
    To,
    Colon,
    Dot,
    LeftBracket,
    RightBracket,
}

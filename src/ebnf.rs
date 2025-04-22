use color_eyre::{Report, Result};
use lexviz::scanner::Token;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum RepetitionType {
    ZeroOrMore,
    OneOrMore,
    ZeroOrOne,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    TerminalLiteral(String),
    TerminalCategory(String),
    NonTerminal(String),
    Group(Box<Vec<Term>>),
    Repetition(Box<Term>, RepetitionType),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expression {
    sequence: Vec<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Production {
    lhs: Term,
    rhs: Vec<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grammar {
    goal: Production,
    productions: Vec<Production>,
}

#[derive(Debug)]
pub enum ParseError {
    IncompleteProductionError,
    MultipleLeftProductions(String, String),
    InvalidProductionLHS(String),
    UnbalancedParenError,
    InvalidTokenErr(String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::UnbalancedParenError => write!(f, "Error: Unbalanced parenthesis!"),
            ParseError::IncompleteProductionError => {
                write!(f, "Error: Production definition is incomplete!")
            }
            ParseError::InvalidProductionLHS(prod) => write!(
                f,
                "Error: {} is not a valid left side for a production!",
                prod
            ),
            ParseError::InvalidTokenErr(token) => {
                write!(f, "Error: {} is not a valid token!", token)
            }
            ParseError::MultipleLeftProductions(term1, term2) => write!(
                f,
                "Error: {} and {} two left hand terms found for a production!",
                term1, term2
            ),
        }
    }
}

impl std::error::Error for ParseError {}

impl Expression {
    pub fn get_terms(&self) -> &Vec<Term> {
        &self.sequence
    }
    fn parse(tokens: &Vec<Token>, start: usize, end: usize) -> Result<Self> {
        let mut sequence: Vec<Term> = Vec::new();

        let mut idx = start;

        while idx <= end {
            let word = &tokens[idx].get_token();
            let category = &tokens[idx].get_category();

            let next_category = if idx == end {
                None
            } else {
                Some(tokens[idx + 1].get_category())
            };

            let term = match category.as_str() {
                "TERMINAL_LITERAL" => Term::TerminalLiteral(word.to_string()),
                "NON_TERMINAL" => Term::NonTerminal(word[1..word.len() - 1].to_string()),
                "TERMINAL_CATEGORY" => Term::TerminalCategory(word.to_string()),
                "LPAREN" => {
                    let mut depth = 1; // Start at depth 1
                    let mut rparen_idx = idx + 1; // Assume rparen is next token

                    while rparen_idx <= end && depth > 0 {
                        // While we are not at the end and the
                        // depth is not 0
                        if tokens[rparen_idx].get_category() == "LPAREN" {
                            depth += 1; // If the token is an LPAREN increase the depth
                        } else if tokens[rparen_idx].get_category() == "RPAREN" {
                            depth -= 1; // If the token is an RPAREN decrease the depth
                        }
                        if depth == 0 {
                            // If the depth is 0, exit
                            break;
                        }
                        rparen_idx += 1; // Move the pointer to the next token
                    }

                    if depth != 0 {
                        let err = Report::new(ParseError::UnbalancedParenError);
                        return Err(err);
                    }

                    let inner_expression = Expression::parse(tokens, idx + 1, rparen_idx - 1)?;
                    idx = rparen_idx;
                    Term::Group(Box::new(inner_expression.sequence))
                }
                _ => {
                    let err = Report::new(ParseError::InvalidTokenErr(
                        tokens[idx].get_token().to_string(),
                    ));
                    return Err(err);
                }
            };

            let term = if next_category.is_none() {
                // No repetition operator
                idx += 1; // Move to next token
                term
            } else {
                match next_category.unwrap().as_str() {
                    "PLUS" => {
                        idx += 2; // Consume the quantifier
                        Term::Repetition(Box::new(term), RepetitionType::OneOrMore)
                    }
                    "ASTERISK" => {
                        idx += 2; // Consume the quantifier
                        Term::Repetition(Box::new(term), RepetitionType::ZeroOrMore)
                    }
                    "QUESTION" => {
                        idx += 2; // Consume the quantifier
                        Term::Repetition(Box::new(term), RepetitionType::ZeroOrOne)
                    }
                    _ => {
                        idx += 1;
                        term
                    } // Not a quantifier move on
                }
            };
            sequence.push(term);
        }

        Ok(Expression { sequence })
    }
}

impl Production {
    pub fn get_expressions(&self) -> &Vec<Expression> {
        return &self.rhs;
    }

    pub fn get_left_term(&self) -> &Term {
        return &self.lhs;
    }

    fn parse(tokens: &Vec<Token>, start: usize, end: usize) -> Result<Self> {
        if tokens[start].get_category() != "NON_TERMINAL" {
            let err = Report::new(ParseError::InvalidProductionLHS(
                tokens[start].get_token().to_string(),
            ));
            return Err(err);
        }
        if tokens[start + 1].get_category() != "DEFINES" {
            let err = Report::new(ParseError::MultipleLeftProductions(
                tokens[start].get_token().to_string(),
                tokens[start + 1].get_token().to_string(),
            ));
            return Err(err);
        }

        let prod = &tokens[start].get_token();

        let lhs = Term::NonTerminal(prod[1..prod.len() - 1].to_string());

        let mut rhs: Vec<Expression> = Vec::new();

        let mut expression_start = start + 2; // Skip the defines

        for pos in expression_start..end {
            if tokens[pos].get_category() == "ALTERNATION" {
                let expression = Expression::parse(tokens, expression_start, pos - 1)?;
                // Parse everything until the alternation as a production rule
                rhs.push(expression);
                expression_start = pos + 1; // Consume the alternation itself
            }
        }

        // Parse the last production rule before the termination
        let expression = Expression::parse(tokens, expression_start, end)?;

        rhs.push(expression);

        Ok(Production { lhs, rhs })
    }
}

impl Grammar {
    pub fn get_goal(&self) -> &Production {
        return &self.goal;
    }

    pub fn get_productions(&self) -> &Vec<Production> {
        return &self.productions;
    }

    fn parse(token_list: Vec<Token>) -> Result<Self> {
        let mut production_start = 0;
        let mut production_end = 0;

        let mut productions: Vec<Production> = Vec::new();

        for (token_number, token) in token_list.iter().enumerate() {
            let category = token.get_category();

            if category == "TERMINATION" {
                production_end = token_number;
                let production =
                    Production::parse(&token_list, production_start, production_end - 1)?;
                production_start = production_end + 1;
                productions.push(production);
            }
        }

        // If we reach end of file before completing a production throw an error
        if production_end != token_list.len() - 1 {
            let err = Report::new(ParseError::IncompleteProductionError);
            return Err(err);
        }

        Ok(Grammar {
            goal: productions[0].clone(),
            productions,
        })
    }
}

/// Read an EBNF file and return the Grammar structure
pub fn parse_grammar(token_list: Vec<Token>) -> Result<Grammar> {
    let parsed_grammar = Grammar::parse(token_list)?;
    //println!("The parsed grammar is {:?}", parsed_grammar);

    return Ok(parsed_grammar);
}

#[cfg(test)]

mod ebnf_parser_test_helpers {
    use lexviz::scanner::Token;

    pub fn get_token(token: &str, category: &str) -> Token {
        Token::new(token.to_string(), category.to_string())
    }
}
#[cfg(test)]

mod ebnf_parser_tests {
    use crate::ebnf::{
        Grammar, ParseError, Production, RepetitionType, Term, ebnf_parser_test_helpers::get_token,
    };
    use lexviz::scanner::Token;

    use super::Expression;

    #[test]
    fn test_expression_parse_terminal() {
        let mut tokens: Vec<Token> = Vec::new();

        tokens.push(get_token("true", "TERMINAL_LITERAL"));

        let expression = Expression::parse(&tokens, 0, 0);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let mut expected_list: Vec<Term> = Vec::new();

        expected_list.push(Term::TerminalLiteral("true".to_string()));

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_terminal_category() {
        let mut tokens: Vec<Token> = Vec::new();

        tokens.push(get_token("NUMBER", "TERMINAL_CATEGORY"));

        let expression = Expression::parse(&tokens, 0, 0);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let mut expected_list: Vec<Term> = Vec::new();

        expected_list.push(Term::TerminalCategory("NUMBER".to_string()));

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_non_terminal() {
        let mut tokens: Vec<Token> = Vec::new();

        tokens.push(get_token("<boolean>", "NON_TERMINAL"));

        let expression = Expression::parse(&tokens, 0, 0);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let mut expected_list: Vec<Term> = Vec::new();

        expected_list.push(Term::NonTerminal("boolean".to_string()));

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_terminal_repeat() {
        let mut tokens: Vec<Token> = Vec::new();

        tokens.push(get_token("true", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\*", "ASTERISK"));

        let expression = Expression::parse(&tokens, 0, 1);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let mut expected_list: Vec<Term> = Vec::new();

        expected_list.push(Term::Repetition(
            Box::new(Term::TerminalLiteral("true".to_string())),
            RepetitionType::ZeroOrMore,
        ));

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_non_terminal_repeat() {
        let mut tokens: Vec<Token> = Vec::new();

        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("\\+", "PLUS"));

        let expression = Expression::parse(&tokens, 0, 1);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let mut expected_list: Vec<Term> = Vec::new();

        expected_list.push(Term::Repetition(
            Box::new(Term::NonTerminal("boolean".to_string())),
            RepetitionType::OneOrMore,
        ));

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_group() {
        let mut tokens: Vec<Token> = Vec::new();

        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "TERMINAL_LITERAL"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(")", "RPAREN"));

        let expression = Expression::parse(&tokens, 0, tokens.len() - 1);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let mut expected_list: Vec<Term> = Vec::new();

        expected_list.push(Term::Group(Box::new(vec![
            Term::TerminalLiteral("5".to_string()),
            Term::TerminalLiteral("+".to_string()),
            Term::Group(Box::new(vec![Term::Repetition(
                Box::new(Term::NonTerminal("boolean".to_string())),
                RepetitionType::ZeroOrOne,
            )])),
        ])));

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_unbalanced_paren() {
        let mut tokens: Vec<Token> = Vec::new();

        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "TERMINAL_LITERAL"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));

        let expression = Expression::parse(&tokens, 0, tokens.len() - 1);

        assert!(expression.is_err());

        let expression = expression.unwrap_err();

        match expression.downcast_ref().unwrap() {
            ParseError::UnbalancedParenError => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_expression_invalid_token() {
        let mut tokens: Vec<Token> = Vec::new();

        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "NUMBER"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(")", "RPAREN"));

        let expression = Expression::parse(&tokens, 0, tokens.len() - 1);

        assert!(expression.is_err());

        let expression = expression.unwrap_err();

        match expression.downcast_ref().unwrap() {
            ParseError::InvalidTokenErr(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_production() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "TERMINAL_LITERAL"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(")", "RPAREN"));

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_ok());

        let production = production.unwrap();

        let mut expression_list: Vec<Term> = Vec::new();

        expression_list.push(Term::Group(Box::new(vec![
            Term::TerminalLiteral("5".to_string()),
            Term::TerminalLiteral("+".to_string()),
            Term::Group(Box::new(vec![Term::Repetition(
                Box::new(Term::NonTerminal("boolean".to_string())),
                RepetitionType::ZeroOrOne,
            )])),
        ])));

        let expected_production = Production {
            lhs: Term::NonTerminal("test".to_string()),
            rhs: vec![Expression {
                sequence: expression_list,
            }],
        };

        assert_eq!(expected_production, production);
    }

    #[test]
    fn test_production_alternation() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "TERMINAL_LITERAL"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token("\\|", "ALTERNATION"));
        tokens.push(get_token("<6>", "NON_TERMINAL"));

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_ok());

        let production = production.unwrap();

        let mut expression_list: Vec<Term> = Vec::new();

        expression_list.push(Term::Group(Box::new(vec![
            Term::TerminalLiteral("5".to_string()),
            Term::TerminalLiteral("+".to_string()),
            Term::Group(Box::new(vec![Term::Repetition(
                Box::new(Term::NonTerminal("boolean".to_string())),
                RepetitionType::ZeroOrOne,
            )])),
        ])));

        let expected_production = Production {
            lhs: Term::NonTerminal("test".to_string()),
            rhs: vec![
                Expression {
                    sequence: expression_list,
                },
                Expression {
                    sequence: vec![Term::NonTerminal("6".to_string())],
                },
            ],
        };

        assert_eq!(expected_production, production);
    }

    #[test]
    fn test_production_invalid_production() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "TERMINAL_LITERAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "TERMINAL_LITERAL"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(")", "RPAREN"));

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_err());

        let result = production.unwrap_err();

        match result.downcast_ref().unwrap() {
            ParseError::InvalidProductionLHS(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_production_missing_defines() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "NON_TERMINAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "TERMINAL_LITERAL"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(")", "RPAREN"));

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_err());

        let result = production.unwrap_err();

        match result.downcast_ref().unwrap() {
            ParseError::MultipleLeftProductions(_, _) => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_grammar() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "TERMINAL_LITERAL"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(";", "TERMINATION"));

        let grammar = Grammar::parse(tokens);

        assert!(grammar.is_ok());

        let grammar = grammar.unwrap();

        let mut expression_list: Vec<Term> = Vec::new();

        expression_list.push(Term::Group(Box::new(vec![
            Term::TerminalLiteral("5".to_string()),
            Term::TerminalLiteral("+".to_string()),
            Term::Group(Box::new(vec![Term::Repetition(
                Box::new(Term::NonTerminal("boolean".to_string())),
                RepetitionType::ZeroOrOne,
            )])),
        ])));

        let expected_production = Production {
            lhs: Term::NonTerminal("test".to_string()),
            rhs: vec![Expression {
                sequence: expression_list.clone(),
            }],
        };

        let expected_grammar = Grammar {
            goal: Production {
                lhs: Term::NonTerminal("test".to_string()),
                rhs: vec![Expression {
                    sequence: expression_list,
                }],
            },
            productions: vec![expected_production],
        };

        assert_eq!(expected_grammar, grammar);
    }

    #[test]
    fn test_grammar_incomplete_production() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("5", "TERMINAL_LITERAL"));
        tokens.push(get_token("+", "TERMINAL_LITERAL"));
        tokens.push(get_token("\\(", "LPAREN"));
        tokens.push(get_token("<boolean>", "NON_TERMINAL"));
        tokens.push(get_token("?", "QUESTION"));
        tokens.push(get_token(")", "RPAREN"));
        tokens.push(get_token(")", "RPAREN"));

        let grammar = Grammar::parse(tokens);

        assert!(grammar.is_err());

        let result = grammar.unwrap_err();

        match result.downcast_ref().unwrap() {
            ParseError::IncompleteProductionError => assert!(true),
            _ => assert!(false),
        }
    }
}

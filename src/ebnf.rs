use std::{collections::HashSet, fmt};

use color_eyre::{Report, Result};
use lexviz::scanner::Token;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RepetitionType {
    ZeroOrMore,
    OneOrMore,
    ZeroOrOne,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    TerminalLiteral(String),
    TerminalCategory(String),
    NonTerminal(String),
    Group(Vec<Term>),
    Repetition(Box<Term>, RepetitionType),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TerminalLiteral(literal) => write!(f, "{}", literal),
            Self::TerminalCategory(category) => write!(f, "{}", category),
            Self::NonTerminal(non_terminal) => write!(f, "<{}>", non_terminal),
            Self::Group(inner_terms) => {
                write!(f, "(")?;
                for term in inner_terms.iter() {
                    write!(f, "{}", term)?;
                }
                write!(f, ")")
            }
            Self::Repetition(term, repetition_type) => match repetition_type {
                RepetitionType::ZeroOrOne => write!(f, "{}?", term),
                RepetitionType::OneOrMore => write!(f, "{}+", term),
                RepetitionType::ZeroOrMore => write!(f, "{}*", term),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expression {
    sequence: Vec<Term>,
    unit_non_terminal: bool,
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for term in self.sequence.iter() {
            write!(f, "{} ", term)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Production {
    lhs: Term,
    rhs: Vec<Expression>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grammar {
    goal: Production,
    productions: Vec<Production>,
}

impl fmt::Display for Grammar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for production in self.productions.iter() {
            let lhs = production.get_left_term();
            write!(f, "{} ::= ", lhs)?;
            let expressions = production.get_expressions();
            for (idx, expression) in expressions.iter().enumerate() {
                write!(f, "{} ", expression)?;
                if idx != expressions.len() - 1 {
                    write!(f, "| ")?;
                }
            }
            writeln!(f, ";")?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum ParseError {
    IncompleteProduction,
    MultipleLeftProductions(String, String),
    InvalidProductionLHS(String),
    UnbalancedParen,
    InvalidToken(String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::UnbalancedParen => write!(f, "Error: Unbalanced parenthesis!"),
            ParseError::IncompleteProduction => {
                write!(f, "Error: Production definition is incomplete!")
            }
            ParseError::InvalidProductionLHS(prod) => write!(
                f,
                "Error: {} is not a valid left side for a production!",
                prod
            ),
            ParseError::InvalidToken(token) => {
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

    pub fn is_non_terminal_unit(&self) -> bool {
        self.unit_non_terminal
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
                        let err = Report::new(ParseError::UnbalancedParen);
                        return Err(err);
                    }

                    let inner_expression = Expression::parse(tokens, idx + 1, rparen_idx - 1)?;
                    idx = rparen_idx;
                    Term::Group(inner_expression.sequence)
                }
                _ => {
                    let err = Report::new(ParseError::InvalidToken(
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

        let is_unit_non_terminal = if sequence.len() == 1 {
            matches!(sequence[0], Term::NonTerminal(_))
        } else {
            false
        };

        Ok(Expression {
            sequence,
            unit_non_terminal: is_unit_non_terminal,
        })
    }
}

impl Production {
    pub fn get_expressions(&self) -> &Vec<Expression> {
        &self.rhs
    }

    pub fn get_left_term(&self) -> &Term {
        &self.lhs
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

        let mut rhs: HashSet<Expression> = HashSet::new();

        let mut expression_start = start + 2; // Skip the defines

        for pos in expression_start..end {
            if tokens[pos].get_category() == "ALTERNATION" {
                let expression = Expression::parse(tokens, expression_start, pos - 1)?;
                // Parse everything until the alternation as a production rule
                rhs.insert(expression);
                expression_start = pos + 1; // Consume the alternation itself
            }
        }

        // Parse the last production rule before the termination
        let expression = Expression::parse(tokens, expression_start, end)?;

        rhs.insert(expression);
        let rhs: Vec<Expression> = rhs.into_iter().collect();

        Ok(Production { lhs, rhs })
    }
}

impl Grammar {
    pub fn get_goal(&self) -> &Production {
        &self.goal
    }

    pub fn get_productions(&self) -> &Vec<Production> {
        &self.productions
    }

    pub fn remove_production(&mut self, removal_list: &Vec<Term>) {
        for prod in removal_list {
            if let Some(pos) = self
                .productions
                .iter()
                .position(|x| *x.get_left_term() == *prod)
            {
                self.productions.remove(pos);
            }
        }
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
            let err = Report::new(ParseError::IncompleteProduction);
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

    Ok(parsed_grammar)
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
    use std::collections::HashSet;

    use crate::ebnf::{
        Grammar, ParseError, Production, RepetitionType, Term, ebnf_parser_test_helpers::get_token,
    };
    use lexviz::scanner::Token;

    use super::Expression;

    #[test]
    fn test_expression_parse_terminal() {
        let tokens: Vec<Token> = vec![get_token("true", "TERMINAL_LITERAL")];

        let expression = Expression::parse(&tokens, 0, 0);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let expected_list: Vec<Term> = vec![Term::TerminalLiteral("true".to_string())];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_terminal_category() {
        let tokens: Vec<Token> = vec![get_token("NUMBER", "TERMINAL_CATEGORY")];

        let expression = Expression::parse(&tokens, 0, 0);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let expected_list: Vec<Term> = vec![Term::TerminalCategory("NUMBER".to_string())];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_non_terminal() {
        let tokens: Vec<Token> = vec![get_token("<boolean>", "NON_TERMINAL")];

        let expression = Expression::parse(&tokens, 0, 0);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let expected_list: Vec<Term> = vec![Term::NonTerminal("boolean".to_string())];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_terminal_repeat() {
        let tokens: Vec<Token> = vec![
            get_token("true", "TERMINAL_LITERAL"),
            get_token("\\*", "ASTERISK"),
        ];

        let expression = Expression::parse(&tokens, 0, 1);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let expected_list: Vec<Term> = vec![Term::Repetition(
            Box::new(Term::TerminalLiteral("true".to_string())),
            RepetitionType::ZeroOrMore,
        )];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_non_terminal_repeat() {
        let tokens: Vec<Token> = vec![
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("\\+", "PLUS"),
        ];

        let expression = Expression::parse(&tokens, 0, 1);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let expected_list: Vec<Term> = vec![Term::Repetition(
            Box::new(Term::NonTerminal("boolean".to_string())),
            RepetitionType::OneOrMore,
        )];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_group() {
        let tokens: Vec<Token> = vec![
            get_token("\\(", "LPAREN"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
            get_token(")", "RPAREN"),
        ];

        let expression = Expression::parse(&tokens, 0, tokens.len() - 1);

        assert!(expression.is_ok());

        let expression = expression.unwrap();

        let sequence = expression.sequence;

        let expected_list: Vec<Term> = vec![Term::Group(vec![
            Term::TerminalLiteral("5".to_string()),
            Term::TerminalLiteral("+".to_string()),
            Term::Group(vec![Term::Repetition(
                Box::new(Term::NonTerminal("boolean".to_string())),
                RepetitionType::ZeroOrOne,
            )]),
        ])];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_unbalanced_paren() {
        let tokens: Vec<Token> = vec![
            get_token("\\(", "LPAREN"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
        ];

        let expression = Expression::parse(&tokens, 0, tokens.len() - 1);

        assert!(expression.is_err());

        let expression = expression.unwrap_err();

        match expression.downcast_ref().unwrap() {
            ParseError::UnbalancedParen => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_expression_invalid_token() {
        let tokens: Vec<Token> = vec![
            get_token("\\(", "LPAREN"),
            get_token("5", "NUMBER"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
            get_token(")", "RPAREN"),
        ];

        let expression = Expression::parse(&tokens, 0, tokens.len() - 1);

        assert!(expression.is_err());

        let expression = expression.unwrap_err();

        match expression.downcast_ref().unwrap() {
            ParseError::InvalidToken(_) => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_production() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\\(", "LPAREN"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
            get_token(")", "RPAREN"),
        ];

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_ok());

        let production = production.unwrap();

        let expression_list: Vec<Term> = vec![Term::Group(vec![
            Term::TerminalLiteral("5".to_string()),
            Term::TerminalLiteral("+".to_string()),
            Term::Group(vec![Term::Repetition(
                Box::new(Term::NonTerminal("boolean".to_string())),
                RepetitionType::ZeroOrOne,
            )]),
        ])];

        let expected_production = Production {
            lhs: Term::NonTerminal("test".to_string()),
            rhs: vec![Expression {
                sequence: expression_list,
                unit_non_terminal: false,
            }],
        };

        assert_eq!(expected_production, production);
    }

    #[test]
    fn test_production_alternation() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\\(", "LPAREN"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
            get_token(")", "RPAREN"),
            get_token("\\|", "ALTERNATION"),
            get_token("<6>", "NON_TERMINAL"),
        ];

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_ok());

        let production = production.unwrap();

        let expression_list: Vec<Term> = vec![Term::Group(vec![
            Term::TerminalLiteral("5".to_string()),
            Term::TerminalLiteral("+".to_string()),
            Term::Group(vec![Term::Repetition(
                Box::new(Term::NonTerminal("boolean".to_string())),
                RepetitionType::ZeroOrOne,
            )]),
        ])];

        let expected_production = Production {
            lhs: Term::NonTerminal("test".to_string()),
            rhs: vec![
                Expression {
                    sequence: expression_list,
                    unit_non_terminal: false,
                },
                Expression {
                    sequence: vec![Term::NonTerminal("6".to_string())],
                    unit_non_terminal: true,
                },
            ],
        };

        let left_term = production.get_left_term();

        let expected_left_term = expected_production.get_left_term();

        assert_eq!(left_term, expected_left_term);

        let expressions: HashSet<_> = production.get_expressions().iter().cloned().collect();
        let expected_expressions: HashSet<_> = expected_production
            .get_expressions()
            .iter()
            .cloned()
            .collect();

        assert_eq!(expressions, expected_expressions);
    }

    #[test]
    fn test_production_invalid_production() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "TERMINAL_LITERAL"),
            get_token("::=", "DEFINES"),
            get_token("\\(", "LPAREN"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
            get_token(")", "RPAREN"),
        ];

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_err());

        let result = production.unwrap_err();

        match result.downcast_ref().unwrap() {
            ParseError::InvalidProductionLHS(_) => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_production_missing_defines() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("\\(", "LPAREN"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
            get_token(")", "RPAREN"),
        ];

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_err());

        let result = production.unwrap_err();

        match result.downcast_ref().unwrap() {
            ParseError::MultipleLeftProductions(_, _) => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_grammar() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\\(", "LPAREN"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
            get_token(")", "RPAREN"),
            get_token(";", "TERMINATION"),
        ];

        let grammar = Grammar::parse(tokens);

        assert!(grammar.is_ok());

        let grammar = grammar.unwrap();

        let expression_list: Vec<Term> = vec![Term::Group(vec![
            Term::TerminalLiteral("5".to_string()),
            Term::TerminalLiteral("+".to_string()),
            Term::Group(vec![Term::Repetition(
                Box::new(Term::NonTerminal("boolean".to_string())),
                RepetitionType::ZeroOrOne,
            )]),
        ])];

        let expected_production = Production {
            lhs: Term::NonTerminal("test".to_string()),
            rhs: vec![Expression {
                sequence: expression_list.clone(),
                unit_non_terminal: false,
            }],
        };

        let expected_grammar = Grammar {
            goal: Production {
                lhs: Term::NonTerminal("test".to_string()),
                rhs: vec![Expression {
                    sequence: expression_list,
                    unit_non_terminal: false,
                }],
            },
            productions: vec![expected_production],
        };

        assert_eq!(expected_grammar, grammar);
    }

    #[test]
    fn test_grammar_incomplete_production() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\\(", "LPAREN"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("+", "TERMINAL_LITERAL"),
            get_token("\\(", "LPAREN"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token(")", "RPAREN"),
            get_token(")", "RPAREN"),
        ];

        let grammar = Grammar::parse(tokens);

        assert!(grammar.is_err());

        let result = grammar.unwrap_err();

        match result.downcast_ref().unwrap() {
            ParseError::IncompleteProduction => {}
            _ => unreachable!(),
        }
    }
}

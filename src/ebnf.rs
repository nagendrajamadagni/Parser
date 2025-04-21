use color_eyre::{Report, Result};
use lexviz::scanner::Token;

#[derive(Debug, Clone)]
pub enum RepetitionType {
    ZeroOrMore,
    OneOrMore,
    ZeroOrOne,
}

#[derive(Debug, Clone)]
pub enum Term {
    Terminal(String),
    NonTerminal(String),
    Group(Box<Vec<Term>>),
    Repetition(Box<Term>, RepetitionType),
}

#[derive(Debug, Clone)]
pub struct Expression {
    sequence: Vec<Term>,
}

#[derive(Debug, Clone)]
pub struct Production {
    lhs: Term,
    rhs: Vec<Expression>,
}

#[derive(Debug, Clone)]
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
                "TERMINAL" => Term::Terminal(word.to_string()),
                "NON_TERMINAL" => Term::NonTerminal(word.to_string()),
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

        let lhs = Term::NonTerminal(prod.to_string());

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
    println!("The parsed grammar is {:?}", parsed_grammar);

    return Ok(parsed_grammar);
}

use std::{
    fs::File,
    io::{BufRead, BufReader},
};

pub enum RepetitionType {
    ZeroOrMore,
    OneOrMore,
    ZeroOrOne,
}

pub enum Term {
    Terminal(String),
    NonTerminal(String),
    Group(Box<Vec<Term>>),
    Repetition(Box<Term>, RepetitionType),
}

pub struct Expression {
    sequence: Vec<Term>,
}

pub struct Production {
    lhs: Term,
    rhs: Vec<Expression>,
}

pub struct Grammar {
    productions: Vec<Production>,
}

impl Expression {
    fn parse(tokens: &Vec<(String, String)>, start: usize, end: usize) -> Self {
        let mut sequence: Vec<Term> = Vec::new();

        let mut idx = start;

        while idx <= end {
            let word = &tokens[idx].0;
            let category = &tokens[idx].1;

            let next_category = if idx == end {
                None
            } else {
                Some(&tokens[idx + 1].1)
            };

            let term = match category.as_str() {
                "TERMINAL" => Term::Terminal(word.clone()),
                "NON_TERMINAL" => Term::NonTerminal(word.clone()),
                "LPAREN" => {
                    let mut depth = 1;
                    let mut rparen_idx = idx + 1;

                    while rparen_idx <= end && depth > 0 {
                        if tokens[rparen_idx].1 == "LPAREN" {
                            depth += 1;
                        } else if tokens[rparen_idx].1 == "RPAREN" {
                            depth -= 1;
                        }
                        if depth == 0 {
                            break;
                        }
                        rparen_idx += 1;
                    }

                    if depth != 0 {
                        panic!("The parenthesis opened on line {} is never closed!", idx);
                    }

                    let inner_expression = Expression::parse(tokens, idx + 1, rparen_idx - 1);
                    idx = rparen_idx;
                    Term::Group(Box::new(inner_expression.sequence))
                }
                _ => {
                    panic!("Invalid {} token found on line {}", tokens[idx].0, idx);
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

        Expression { sequence }
    }
}

impl Production {
    fn parse(tokens: &Vec<(String, String)>, start: usize, end: usize) -> Self {
        if tokens[start].1 != "NON_TERMINAL" {
            panic!(
                "Left hand side of production is not a non terminal symbol! Found {}",
                tokens[start].0
            );
        }
        if tokens[start + 1].1 != "DEFINES" {
            panic!(
                "Left hand side of production has multiple terms! Found {} {}",
                tokens[start].0,
                tokens[start + 1].0
            );
        }

        let lhs = Term::NonTerminal(tokens[start].0.clone());

        let mut rhs: Vec<Expression> = Vec::new();

        let mut expression_start = start + 2;

        for pos in expression_start..end {
            if tokens[pos].1 == "ALTERNATION" {
                let expression = Expression::parse(tokens, expression_start, pos - 1);
                rhs.push(expression);
                expression_start = pos + 1; // Consume the alternation itself
            }
        }
        let expression = Expression::parse(tokens, expression_start, end);
        rhs.push(expression);

        Production { lhs, rhs }
    }
}

impl Grammar {
    fn parse(file: File) -> Self {
        let reader = BufReader::new(file);
        let mut production_start = 0;
        let mut production_end = 0;
        let mut lexed_lines: Vec<(String, String)> = Vec::new();

        let mut productions: Vec<Production> = Vec::new();

        for (line_number, line) in reader.lines().enumerate() {
            let content = match line {
                Ok(content) => content,
                Err(err) => panic!("Error reading line! {:?}", err),
            };

            if !content.starts_with('(') || !content.ends_with(')') {
                panic!("Invalid line provided! {}", content);
            }

            let content = &content[1..content.len() - 1];

            if let Some(last_comma_index) = content.rfind(',') {
                let word = &content[..last_comma_index].trim();
                let category = &content[last_comma_index + 1..].trim();

                lexed_lines.push((word.to_string(), category.to_string()));

                if *category == "TERMINATION" {
                    production_end = line_number;
                    let production =
                        Production::parse(&lexed_lines, production_start, production_end - 1);
                    production_start = production_end + 1;
                    productions.push(production);
                }
            } else {
                panic!("Invalid line provided {}", content);
            }
        }

        // If we reach end of file before completing a production print an error
        if production_end != lexed_lines.len() - 1 {
            panic!(
                "The production started at line {} has not been terminated!",
                production_start
            );
        }

        Grammar { productions }
    }
}

pub fn parse_grammar(file_path: &str) -> Grammar {
    let file = match File::open(file_path) {
        Ok(file) => file,
        Err(err) => panic!(
            "Could not open the provided file {:?}! {:?}",
            file_path, err
        ),
    };
    let parsed_grammar = Grammar::parse(file);

    return parsed_grammar;
}

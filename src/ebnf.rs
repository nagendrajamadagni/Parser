use color_eyre::{Report, Result};
use lexviz::scanner::Token;
use std::{collections::HashSet, fmt};

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
            Self::TerminalCategory(category) => {
                if category == "EPSILON" {
                    write!(f, "𝛆")
                } else {
                    write!(f, "{}", category)
                }
            }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Production {
    lhs: Term,
    rhs: Vec<Vec<Term>>,
    terminal_set: HashSet<Term>,
    non_terminal_set: HashSet<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grammar {
    goal: Term,
    productions: Vec<Production>,
}

impl fmt::Display for Grammar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for production in self.productions.iter() {
            let lhs = production.get_left_term();
            write!(f, "{} ::= ", lhs)?;
            let expressions = production.get_expressions();
            for (idx, expression) in expressions.iter().enumerate() {
                for term in expression {
                    write!(f, "{} ", term)?;
                }
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

impl Production {
    fn parse_expression(tokens: &Vec<Token>, start: usize, end: usize) -> Result<Vec<Term>> {
        let mut sequence: Vec<Term> = Vec::new();

        let mut idx = start;

        while idx <= end {
            let word = &tokens[idx].get_token();
            let category = &tokens[idx].get_category();

            let mut next_category = if idx == end {
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

                    let inner_expression = Self::parse_expression(tokens, idx + 1, rparen_idx - 1)?;
                    idx = rparen_idx;
                    next_category = if idx == end {
                        // Now that we parsed the inner expression and
                        // moved the pointer, we need to recheck the
                        // next category
                        None
                    } else {
                        Some(tokens[idx + 1].get_category())
                    };
                    Term::Group(inner_expression)
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

        if sequence.is_empty() {
            let err = Report::new(ParseError::IncompleteProduction);
            return Err(err);
        }

        Ok(sequence)
    }

    pub fn get_expressions_mut(&mut self) -> &mut Vec<Vec<Term>> {
        &mut self.rhs
    }

    pub fn get_expressions(&self) -> &Vec<Vec<Term>> {
        &self.rhs
    }

    pub fn get_left_term(&self) -> &Term {
        &self.lhs
    }

    fn parse(tokens: &Vec<Token>, start: usize, end: usize) -> Result<Self> {
        let terminal_set = HashSet::new();
        let non_terminal_set = HashSet::new();

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

        //let mut rhs: HashSet<Expression> = HashSet::new();
        let mut rhs: Vec<Vec<Term>> = Vec::new();

        let mut expression_start = start + 2; // Skip the defines
        let mut deduplication_set: HashSet<Vec<Term>> = HashSet::new();

        for pos in expression_start..end {
            if tokens[pos].get_category() == "ALTERNATION" {
                let expression: Vec<Term> =
                    Self::parse_expression(tokens, expression_start, pos - 1)?;
                // Parse everything until the alternation as a production rule

                if !deduplication_set.contains(&expression) {
                    rhs.push(expression.clone());
                    deduplication_set.insert(expression);
                }
                expression_start = pos + 1; // Consume the alternation itself
            }
        }

        // Parse the last production rule before the termination
        let expression = Self::parse_expression(tokens, expression_start, end)?;

        if !deduplication_set.contains(&expression) {
            rhs.push(expression.clone());
            deduplication_set.insert(expression);
        }

        Ok(Production {
            lhs,
            rhs,
            terminal_set,
            non_terminal_set,
        })
    }

    fn get_terminal_terms(expression: &Vec<Term>) -> HashSet<Term> {
        let mut terminal_set = HashSet::new();

        for term in expression {
            match term {
                Term::TerminalLiteral(_) => {
                    terminal_set.insert(term.clone());
                }
                Term::TerminalCategory(_) => {
                    terminal_set.insert(term.clone());
                }
                Term::NonTerminal(_) => {}
                Term::Group(group) => {
                    let group_terminals = Self::get_terminal_terms(group);
                    terminal_set.extend(group_terminals);
                }
                Term::Repetition(boxed_term, _) => {
                    let boxed_term = boxed_term.clone();
                    let repetition_terminals = Self::get_terminal_terms(&vec![*boxed_term]);
                    terminal_set.extend(repetition_terminals);
                }
            };
        }

        terminal_set
    }

    fn get_non_terminal_terms(expression: &Vec<Term>) -> HashSet<Term> {
        let mut non_terminal_set = HashSet::new();

        for term in expression {
            match term {
                Term::TerminalLiteral(_) => {}
                Term::TerminalCategory(_) => {}
                Term::NonTerminal(_) => {
                    non_terminal_set.insert(term.clone());
                }
                Term::Group(group) => {
                    let group_terminals = Self::get_non_terminal_terms(group);
                    non_terminal_set.extend(group_terminals);
                }
                Term::Repetition(boxed_term, _) => {
                    let boxed_term = boxed_term.clone();
                    let repetition_terminals = Self::get_non_terminal_terms(&vec![*boxed_term]);
                    non_terminal_set.extend(repetition_terminals);
                }
            };
        }

        non_terminal_set
    }

    // Return all unit non terminals associated with this production

    pub fn get_unit_non_terminals(&self) -> Vec<Term> {
        self.rhs
            .iter()
            .filter_map(|exp| {
                if exp.len() == 1 && matches![exp.first().unwrap(), Term::NonTerminal(_)] {
                    exp.first().cloned()
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn remove_unit_expression(&mut self, key: Term) {
        self.rhs.retain(|exp| exp.len() != 1 || exp[0] != key);
    }

    pub fn get_non_unit_expressions(&self) -> Vec<Vec<Term>> {
        self.rhs
            .iter()
            .filter(|exp| exp.len() != 1 || !matches![exp[0], Term::NonTerminal(_)])
            .cloned()
            .collect()
    }

    pub fn add_expression(&mut self, expressions: &Vec<Vec<Term>>) {
        let mut deduplication_set: HashSet<Vec<Term>> = HashSet::new();
        deduplication_set.extend(self.rhs.clone());
        for expression in expressions {
            if !deduplication_set.contains(expression) {
                self.rhs.push(expression.clone());
                deduplication_set.insert(expression.clone());
            }
        }
    }

    pub fn remove_expression(&mut self, expression: &Vec<Term>) {
        self.rhs.retain(|exp| exp != expression);
    }

    pub fn get_terminal_set(&self) -> &HashSet<Term> {
        &self.terminal_set
    }

    pub fn get_non_terminal_set(&self) -> &HashSet<Term> {
        &self.non_terminal_set
    }
}

impl Grammar {
    pub fn get_terminal_terms(&mut self) {
        for production in self.productions.iter_mut() {
            production.terminal_set = HashSet::new();
            for expression in &production.rhs {
                let terminal_terms = Production::get_terminal_terms(expression);
                production.terminal_set.extend(terminal_terms);
            }
        }
    }

    pub fn get_non_terminal_terms(&mut self) {
        for production in self.productions.iter_mut() {
            production.non_terminal_set = HashSet::new();
            for expression in &production.rhs {
                let non_terminal_terms = Production::get_non_terminal_terms(expression);
                production.non_terminal_set.extend(non_terminal_terms);
            }
        }
    }
    pub fn get_goal(&self) -> &Term {
        &self.goal
    }

    pub fn find_production_mut(&mut self, key: &Term) -> Option<&mut Production> {
        self.productions
            .iter_mut()
            .find(|p| p.get_left_term() == key)
    }

    pub fn find_production(&self, key: &Term) -> Option<&Production> {
        self.productions.iter().find(|p| p.get_left_term() == key)
    }

    pub fn get_productions(&self) -> &Vec<Production> {
        &self.productions
    }

    pub fn get_productions_mut(&mut self) -> &mut Vec<Production> {
        &mut self.productions
    }

    pub fn remove_definition(&mut self, removal_list: &Vec<Term>) {
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

    pub fn add_definition(&mut self, left_term: Term, definition: Vec<Vec<Term>>) {
        match self.find_production_mut(&left_term) {
            Some(production) => {
                production.add_expression(&definition);
            }
            None => {
                let new_production = Production {
                    lhs: left_term,
                    rhs: definition,
                    terminal_set: HashSet::new(),
                    non_terminal_set: HashSet::new(),
                };
                self.productions.push(new_production);
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
            goal: productions[0].get_left_term().clone(),
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

    use crate::ebnf::{
        Grammar, ParseError, Production, RepetitionType, Term, ebnf_parser_test_helpers::get_token,
    };
    use lexviz::scanner::Token;
    use std::collections::HashSet;

    #[test]
    fn test_expression_parse_terminal() {
        let tokens: Vec<Token> = vec![get_token("true", "TERMINAL_LITERAL")];

        let expression = Production::parse_expression(&tokens, 0, 0);

        assert!(expression.is_ok());

        let sequence = expression.unwrap();

        let expected_list: Vec<Term> = vec![Term::TerminalLiteral("true".to_string())];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_terminal_category() {
        let tokens: Vec<Token> = vec![get_token("NUMBER", "TERMINAL_CATEGORY")];

        let expression = Production::parse_expression(&tokens, 0, 0);

        assert!(expression.is_ok());

        let sequence = expression.unwrap();

        let expected_list: Vec<Term> = vec![Term::TerminalCategory("NUMBER".to_string())];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_non_terminal() {
        let tokens: Vec<Token> = vec![get_token("<boolean>", "NON_TERMINAL")];

        let expression = Production::parse_expression(&tokens, 0, 0);

        assert!(expression.is_ok());

        let sequence = expression.unwrap();

        let expected_list: Vec<Term> = vec![Term::NonTerminal("boolean".to_string())];

        assert_eq!(sequence, expected_list);
    }

    #[test]
    fn test_expression_parse_terminal_repeat() {
        let tokens: Vec<Token> = vec![
            get_token("true", "TERMINAL_LITERAL"),
            get_token("\\*", "ASTERISK"),
        ];

        let expression = Production::parse_expression(&tokens, 0, 1);

        assert!(expression.is_ok());

        let sequence = expression.unwrap();

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

        let expression = Production::parse_expression(&tokens, 0, 1);

        assert!(expression.is_ok());

        let sequence = expression.unwrap();

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

        let expression = Production::parse_expression(&tokens, 0, tokens.len() - 1);

        assert!(expression.is_ok());

        let sequence = expression.unwrap();

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

        let expression = Production::parse_expression(&tokens, 0, tokens.len() - 1);

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

        let expression = Production::parse_expression(&tokens, 0, tokens.len() - 1);

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
            rhs: Vec::from([expression_list.clone()]),
            terminal_set: HashSet::new(),
            non_terminal_set: HashSet::new(),
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
            rhs: Vec::from([
                expression_list.clone(),
                vec![Term::NonTerminal("6".to_string())],
            ]),
            terminal_set: HashSet::new(),
            non_terminal_set: HashSet::new(),
        };

        assert_eq!(production, expected_production);
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
            rhs: Vec::from([expression_list.clone()]),
            terminal_set: HashSet::new(),
            non_terminal_set: HashSet::new(),
        };

        let expected_grammar = Grammar {
            goal: Term::NonTerminal("test".to_string()),

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

    #[test]
    fn test_production_unit_non_terminals() {
        let tokens: Vec<Token> = vec![
            get_token("<A>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
            get_token("\\|", "ALTERNATION"),
            get_token("<C>", "NON_TERMINAL"),
        ];

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_ok());

        let production = production.unwrap();

        let unit_non_terminals = production.get_unit_non_terminals();

        let expected_list = vec![Term::NonTerminal("C".to_string())];

        assert_eq!(unit_non_terminals, expected_list);
    }

    #[test]
    fn test_production_unit_no_non_terminals() {
        let tokens: Vec<Token> = vec![
            get_token("<A>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("5", "TERMINAL_LITERAL"),
            get_token("<boolean>", "NON_TERMINAL"),
            get_token("?", "QUESTION"),
        ];

        let production = Production::parse(&tokens, 0, tokens.len() - 1);

        assert!(production.is_ok());

        let production = production.unwrap();

        let unit_non_terminals = production.get_unit_non_terminals();

        assert!(unit_non_terminals.is_empty());
    }

    #[test]
    fn test_production_missing_definition() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\"a\"", "TERMINAL_LITERAL"),
            get_token("<nt2>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<nt2>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token(";", "TERMINATION"),
        ];

        let grammar = Grammar::parse(tokens);

        assert!(grammar.is_err(), "{:?}", grammar);

        let result = grammar.unwrap_err();

        match result.downcast().unwrap() {
            ParseError::IncompleteProduction => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_get_terminal_terms() {
        let terms: Vec<Term> = vec![
            Term::TerminalLiteral("term1".to_string()),
            Term::TerminalCategory("term2".to_string()),
            Term::Group(vec![
                Term::TerminalLiteral("term3".to_string()),
                Term::NonTerminal("nonterm1".to_string()),
            ]),
            Term::NonTerminal("nonterm2".to_string()),
            Term::Repetition(
                Box::new(Term::TerminalLiteral("term4".to_string())),
                RepetitionType::OneOrMore,
            ),
            Term::Repetition(
                Box::new(Term::TerminalCategory("term5".to_string())),
                RepetitionType::OneOrMore,
            ),
            Term::Repetition(
                Box::new(Term::NonTerminal("nonterm3".to_string())),
                RepetitionType::OneOrMore,
            ),
        ];

        let terminal_set = Production::get_terminal_terms(&terms);

        let expected_set = HashSet::from([
            Term::TerminalLiteral("term1".to_string()),
            Term::TerminalCategory("term2".to_string()),
            Term::TerminalLiteral("term3".to_string()),
            Term::TerminalLiteral("term4".to_string()),
            Term::TerminalCategory("term5".to_string()),
        ]);

        assert_eq!(terminal_set, expected_set);
    }

    #[test]
    fn test_get_non_terminal_terms() {
        let terms: Vec<Term> = vec![
            Term::TerminalLiteral("term1".to_string()),
            Term::TerminalCategory("term2".to_string()),
            Term::Group(vec![
                Term::TerminalLiteral("term3".to_string()),
                Term::NonTerminal("nonterm1".to_string()),
            ]),
            Term::NonTerminal("nonterm2".to_string()),
            Term::Repetition(
                Box::new(Term::TerminalLiteral("term4".to_string())),
                RepetitionType::OneOrMore,
            ),
            Term::Repetition(
                Box::new(Term::TerminalCategory("term5".to_string())),
                RepetitionType::OneOrMore,
            ),
            Term::Repetition(
                Box::new(Term::NonTerminal("nonterm3".to_string())),
                RepetitionType::OneOrMore,
            ),
        ];

        let non_terminal_set = Production::get_non_terminal_terms(&terms);

        let expected_set = HashSet::from([
            Term::NonTerminal("nonterm1".to_string()),
            Term::NonTerminal("nonterm2".to_string()),
            Term::NonTerminal("nonterm3".to_string()),
        ]);

        assert_eq!(non_terminal_set, expected_set);
    }
}

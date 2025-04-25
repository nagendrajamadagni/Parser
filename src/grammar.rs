use std::collections::{HashMap, HashSet, VecDeque};

use crate::ebnf::Expression;
pub use crate::ebnf::{Grammar, Production, Term};
use eyre::{Report, Result};

#[derive(Debug)]
pub struct VerifiedGrammar {
    grammar: Grammar,
    term_to_terminal_map: HashMap<Term, HashSet<Term>>,
    term_to_non_terminal_map: HashMap<Term, HashSet<Term>>,
}

#[derive(Debug)]
pub enum GrammarError {
    IncompleteGrammarError(String),
    ProductionNotDefinedError(Vec<Term>),
    NonProductiveError(Vec<Term>),
}

impl std::fmt::Display for GrammarError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IncompleteGrammarError(production) => write!(
                f,
                "Error: Incomplete grammar found, cannot find any expressions for the production {production}"
            ),
            Self::ProductionNotDefinedError(term) => {
                write!(f, "Error: Undefined terms {:?} encountered", term)
            }
            Self::NonProductiveError(terms) => {
                write!(f, "Error: Non productive cycle {:?} detected!", terms)
            }
        }
    }
}

impl std::error::Error for GrammarError {}

// Get list of non terminals in rhs of a grammar
fn get_rhs_non_terminals(
    grammar: &Grammar,
    term_to_non_terminal_map: &mut HashMap<Term, HashSet<Term>>,
    term_to_terminal_map: &mut HashMap<Term, HashSet<Term>>,
) -> HashSet<Term> {
    let mut non_terminals: HashSet<Term> = HashSet::new();
    for production in grammar.get_productions() {
        let lhs = production.get_left_term();
        for expression in production.get_expressions() {
            get_non_terminals_from_expression(
                expression,
                term_to_non_terminal_map,
                term_to_terminal_map,
                lhs,
            );
        }
    }

    let non_terminals_list: Vec<Term> = term_to_non_terminal_map
        .values()
        .flat_map(|set| set.iter())
        .cloned()
        .collect();

    non_terminals.extend(non_terminals_list);

    return non_terminals;
}

// Get list of non terminals from an expression
fn get_non_terminals_from_expression(
    expression: &Expression,
    term_to_non_terminal_map: &mut HashMap<Term, HashSet<Term>>,
    term_to_terminal_map: &mut HashMap<Term, HashSet<Term>>,
    lhs: &Term,
) {
    for term in expression.get_terms() {
        get_non_terminals_from_term(term, term_to_non_terminal_map, term_to_terminal_map, lhs);
    }
}

// Get list of non terminals from a term
fn get_non_terminals_from_term(
    term: &Term,
    term_to_non_terminal_map: &mut HashMap<Term, HashSet<Term>>,
    term_to_terminal_map: &mut HashMap<Term, HashSet<Term>>,
    lhs: &Term,
) {
    match term {
        Term::NonTerminal(_) => {
            term_to_non_terminal_map
                .entry(lhs.clone())
                .or_insert_with(HashSet::new)
                .insert(term.clone());
        }
        Term::Group(terms) => {
            for inner_term in terms.iter() {
                get_non_terminals_from_term(
                    inner_term,
                    term_to_non_terminal_map,
                    term_to_terminal_map,
                    lhs,
                );
            }
        }
        Term::Repetition(term, _) => {
            get_non_terminals_from_term(term, term_to_non_terminal_map, term_to_terminal_map, lhs);
        }
        Term::TerminalLiteral(_) | Term::TerminalCategory(_) => {
            term_to_terminal_map
                .entry(lhs.clone())
                .or_insert_with(HashSet::new)
                .insert(term.clone());
        }
    }
}

// Check if a non-terminal term has atleast one production rule
fn check_non_terminal_productions(production: &Production) -> Result<()> {
    let expressions = production.get_expressions();
    let term = production.get_left_term();

    let term_name = match term {
        Term::NonTerminal(term_name) => term_name,
        _ => panic!("Expected a non-terminal term"),
    };

    if expressions.len() == 0 {
        // If there are not expressions return incomplete grammar
        let err = Report::new(GrammarError::IncompleteGrammarError(term_name.to_string()));
        return Err(err);
    }

    // If the expression definition is an empty list, also return an error
    if expressions.len() == 1 && expressions[0].get_terms().len() == 0 {
        let err = Report::new(GrammarError::IncompleteGrammarError(term_name.to_string()));
        return Err(err);
    }

    return Ok(());
}

// Check if all left hand non-terminal terms have atleast one production term
fn check_lhs_non_terminals(grammar: &Grammar) -> Result<HashSet<Term>> {
    let mut complete_left_productions = HashSet::new();

    // Get list of left terms which are non-terminal productions

    let non_terminal_productions =
        grammar
            .get_productions()
            .iter()
            .filter(|production| match production.get_left_term() {
                Term::NonTerminal(_) => true,
                _ => false,
            });

    // Check if every left non_terminal has atleast one production rule

    for production in non_terminal_productions {
        match check_non_terminal_productions(production) {
            Ok(()) => complete_left_productions.insert(production.get_left_term().clone()),
            Err(err) => return Err(err),
        };
    }

    return Ok(complete_left_productions);
}

// Check if all non terminals used in the RHS are defined, return list of all defined terms or
// error.
fn check_completeness(
    grammar: &Grammar,
    term_to_non_terminal_map: &mut HashMap<Term, HashSet<Term>>,
    term_to_terminal_map: &mut HashMap<Term, HashSet<Term>>,
) -> Result<HashSet<Term>> {
    let used_rhs_non_terminals =
        get_rhs_non_terminals(grammar, term_to_non_terminal_map, term_to_terminal_map);

    let defined_lhs_non_terminals = check_lhs_non_terminals(grammar)?;

    if used_rhs_non_terminals.is_subset(&defined_lhs_non_terminals) {
        return Ok(defined_lhs_non_terminals);
    } else {
        let difference: Vec<_> = used_rhs_non_terminals
            .difference(&defined_lhs_non_terminals)
            .cloned()
            .collect();
        let err = Report::new(GrammarError::ProductionNotDefinedError(difference));
        return Err(err);
    }
}

// Check for any dead code

fn check_reachability(
    term_to_non_terminal_map: &HashMap<Term, HashSet<Term>>,
    goal: &Term,
    defined_terms: &HashSet<Term>,
) -> Result<()> {
    let mut visited: HashSet<Term> = HashSet::new();
    let mut stack: VecDeque<&Term> = VecDeque::new();

    stack.push_front(goal);

    while !stack.is_empty() {
        let term = stack.pop_front().unwrap();
        if visited.contains(term) {
            continue;
        } else {
            visited.insert(term.clone());
        }
        match term_to_non_terminal_map.get(term) {
            Some(terms) => {
                stack.extend(terms.iter());
            }
            None => {}
        }
    }

    let non_reachable: Vec<Term> = defined_terms.difference(&visited).cloned().collect();

    if !non_reachable.is_empty() {
        println!("Found some dead code {:?}", non_reachable);
    }
    return Ok(());
}

// Ensure that there are no unproductive cycles

fn check_productivity(
    term_to_non_terminal_map: &HashMap<Term, HashSet<Term>>,
    term_to_terminal_map: &HashMap<Term, HashSet<Term>>,
    defined_terms: &HashSet<Term>,
) -> Result<()> {
    let mut productive: HashSet<Term> = HashSet::new();

    for term in term_to_terminal_map.keys() {
        productive.insert(term.clone());
    }

    loop {
        let num_productive = productive.len();

        for term in defined_terms {
            // If the term is already productive continue
            if productive.contains(term) {
                continue;
            }

            if term_to_terminal_map.contains_key(term) {
                // If the term has atleast one terminal,
                // mark it as productive and continue
                productive.insert(term.clone());
                continue;
            }

            // Get all non_terminals referenced by the term

            let non_terminals = term_to_non_terminal_map.get(term).unwrap();

            for non_terminal in non_terminals {
                // If the term has atleast one productive non-terminal, mark it as productive and
                // continue.
                if productive.contains(non_terminal) {
                    productive.insert(term.clone());
                    continue;
                }
            }
        }

        if num_productive == productive.len() {
            break;
        }
    }

    let non_productive: Vec<Term> = defined_terms.difference(&productive).cloned().collect();

    if !non_productive.is_empty() {
        let err = Report::new(GrammarError::NonProductiveError(non_productive));
        return Err(err);
    }

    Ok(())
}

pub fn check_correctness(grammar: &Grammar) -> Result<VerifiedGrammar> {
    // Mapping of the non-terminals found in each term
    let mut term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();
    // Mapping of the terminals found in each term
    let mut term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();
    let used_terms = check_completeness(
        grammar,
        &mut term_to_non_terminal_map,
        &mut term_to_terminal_map,
    )?;
    check_reachability(
        &term_to_non_terminal_map,
        grammar.get_goal().get_left_term(),
        &used_terms,
    )?;

    check_productivity(
        &term_to_non_terminal_map,
        &term_to_terminal_map,
        &used_terms,
    )?;

    let verified_grammar = VerifiedGrammar {
        grammar: grammar.clone(),
        term_to_terminal_map: term_to_terminal_map.clone(),
        term_to_non_terminal_map: term_to_non_terminal_map.clone(),
    };

    println!(
        "The verified grammar is {}, the term to non terminal mapping is {:?} and the term to terminal mapping is {:?} and the used terms are {:?}",
        grammar, term_to_non_terminal_map, term_to_terminal_map, used_terms
    );

    Ok(verified_grammar)
}

mod grammar_tests_helper {
    use lexviz::scanner::Token;

    pub fn get_token(token: &str, category: &str) -> Token {
        Token::new(token.to_string(), category.to_string())
    }
}

#[cfg(test)]
mod grammar_tests {
    use std::collections::{HashMap, HashSet};

    use lexviz::scanner::Token;

    use crate::{
        ebnf::{self, Term},
        grammar::{GrammarError, check_productivity, check_reachability},
    };

    use super::{check_completeness, grammar_tests_helper::get_token};

    #[test]
    fn test_goal_complete_successful() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("\"a\"", "TERMINAL_LITERAL"));
        tokens.push(get_token("<nt2>", "NON_TERMINAL"));
        tokens.push(get_token(";", "TERMINATION"));
        tokens.push(get_token("<nt2>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("B", "TERMINAL_CATEGORY"));
        tokens.push(get_token(";", "TERMINATION"));

        let grammar = ebnf::parse_grammar(tokens);

        assert!(grammar.is_ok());

        let grammar = grammar.unwrap();

        let mut term_to_non_terminal_map = HashMap::new();
        let mut term_to_terminal_map = HashMap::new();

        let defined_terms = check_completeness(
            &grammar,
            &mut term_to_non_terminal_map,
            &mut term_to_terminal_map,
        );

        assert!(defined_terms.is_ok());

        let defined_terms = defined_terms.unwrap();

        let mut expected_result: HashSet<Term> = HashSet::new();

        expected_result.insert(Term::NonTerminal("test".to_string()));
        expected_result.insert(Term::NonTerminal("nt2".to_string()));

        assert_eq!(defined_terms, expected_result);

        let mut expected_non_terminal_set: HashSet<Term> = HashSet::new();
        expected_non_terminal_set.insert(Term::NonTerminal("nt2".to_string()));

        let mut expected_term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        expected_term_to_non_terminal_map.insert(
            Term::NonTerminal("test".to_string()),
            expected_non_terminal_set,
        );

        assert_eq!(term_to_non_terminal_map, expected_term_to_non_terminal_map);

        let mut expected_term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalLiteral("\"a\"".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("test".to_string()), expected_terminal_set);

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalCategory("B".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("nt2".to_string()), expected_terminal_set);

        assert_eq!(term_to_terminal_map, expected_term_to_terminal_map);

        let result = check_reachability(
            &term_to_non_terminal_map,
            grammar.get_goal().get_left_term(),
            &defined_terms,
        );

        assert!(result.is_ok());

        let result = check_productivity(
            &term_to_non_terminal_map,
            &term_to_terminal_map,
            &defined_terms,
        );

        assert!(result.is_ok());
    }

    #[test]
    fn test_complete_unsuccessful() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("\"a\"", "TERMINAL_LITERAL"));
        tokens.push(get_token("<nt2>", "NON_TERMINAL"));
        tokens.push(get_token(";", "TERMINATION"));

        let grammar = ebnf::parse_grammar(tokens);

        assert!(grammar.is_ok());

        let grammar = grammar.unwrap();

        let mut term_to_non_terminal_map = HashMap::new();
        let mut term_to_terminal_map = HashMap::new();

        let result = check_completeness(
            &grammar,
            &mut term_to_non_terminal_map,
            &mut term_to_terminal_map,
        );

        assert!(result.is_err());

        let result = result.unwrap_err();

        match result.downcast().unwrap() {
            GrammarError::ProductionNotDefinedError(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_complete_unsuccessful2() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<test>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("\"a\"", "TERMINAL_LITERAL"));
        tokens.push(get_token("<nt2>", "NON_TERMINAL"));
        tokens.push(get_token(";", "TERMINATION"));
        tokens.push(get_token("<nt2>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token(";", "TERMINATION"));

        let grammar = ebnf::parse_grammar(tokens);

        assert!(grammar.is_ok(), "{:?}", grammar);

        let grammar = grammar.unwrap();

        let mut term_to_non_terminal_map = HashMap::new();
        let mut term_to_terminal_map = HashMap::new();

        let result = check_completeness(
            &grammar,
            &mut term_to_non_terminal_map,
            &mut term_to_terminal_map,
        );

        assert!(result.is_err());

        let result = result.unwrap_err();

        match result.downcast().unwrap() {
            GrammarError::IncompleteGrammarError(_) => assert!(true),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_reachability_unsuccessful() {}

    #[test]
    fn test_productivity_unsuccessful() {
        let mut tokens: Vec<Token> = Vec::new();
        tokens.push(get_token("<A>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("<B>", "NON_TERMINAL"));
        tokens.push(get_token(";", "TERMINATION"));
        tokens.push(get_token("<B>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("<C>", "NON_TERMINAL"));
        tokens.push(get_token(";", "TERMINATION"));
        tokens.push(get_token("<C>", "NON_TERMINAL"));
        tokens.push(get_token("::=", "DEFINES"));
        tokens.push(get_token("<A>", "NON_TERMINAL"));
        tokens.push(get_token(";", "TERMINATION"));

        let grammar = ebnf::parse_grammar(tokens);

        assert!(grammar.is_ok());

        let grammar = grammar.unwrap();

        let mut term_to_non_terminal_map = HashMap::new();
        let mut term_to_terminal_map = HashMap::new();

        let defined_terms = check_completeness(
            &grammar,
            &mut term_to_non_terminal_map,
            &mut term_to_terminal_map,
        );

        assert!(defined_terms.is_ok());

        let defined_terms = defined_terms.unwrap();

        let mut expected_result: HashSet<Term> = HashSet::new();

        expected_result.insert(Term::NonTerminal("A".to_string()));
        expected_result.insert(Term::NonTerminal("B".to_string()));
        expected_result.insert(Term::NonTerminal("C".to_string()));

        let result = check_productivity(
            &term_to_non_terminal_map,
            &term_to_terminal_map,
            &defined_terms,
        );

        assert!(result.is_err());

        let result = result.unwrap_err();

        match result.downcast_ref().unwrap() {
            GrammarError::NonProductiveError(_) => assert!(true),
            _ => assert!(false),
        }
    }
}

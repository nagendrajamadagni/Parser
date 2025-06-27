use std::collections::{HashMap, HashSet, VecDeque};

pub use crate::ebnf::{Grammar, Term};
use eyre::{Report, Result};

#[derive(Debug)]
pub enum GrammarError {
    ProductionNotDefined(Vec<Term>),
    NonProductive(Vec<Term>),
}

impl std::fmt::Display for GrammarError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ProductionNotDefined(term) => {
                write!(f, "Error: Undefined terms {:?} encountered", term)
            }
            Self::NonProductive(terms) => {
                write!(f, "Error: Non productive cycle {:?} detected!", terms)
            }
        }
    }
}

impl std::error::Error for GrammarError {}

// Check if all non terminals used in the RHS are defined, return list of all defined terms or
// error.
fn check_completeness(grammar: &Grammar) -> Result<HashSet<Term>> {
    let mut used_rhs_non_terminals: HashSet<Term> = HashSet::new();

    for production in grammar.get_productions() {
        used_rhs_non_terminals.extend(production.get_non_terminal_set().clone());
    }

    let defined_lhs_non_terminals = grammar
        .get_productions()
        .iter()
        .map(|production| production.get_left_term().clone())
        .collect();

    if used_rhs_non_terminals.is_subset(&defined_lhs_non_terminals) {
        Ok(defined_lhs_non_terminals)
    } else {
        let difference: Vec<_> = used_rhs_non_terminals
            .difference(&defined_lhs_non_terminals)
            .cloned()
            .collect();
        let err = Report::new(GrammarError::ProductionNotDefined(difference));
        Err(err)
    }
}

// Check for any dead code

fn check_reachability(
    goal: &Term,
    defined_terms: &HashSet<Term>,
    term_to_non_terminal_map: &HashMap<Term, HashSet<Term>>,
) -> Result<Vec<Term>> {
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

        if let Some(terms) = term_to_non_terminal_map.get(term) {
            stack.extend(terms.iter());
        }
    }

    let non_reachable: Vec<Term> = defined_terms.difference(&visited).cloned().collect();

    if !non_reachable.is_empty() {
        println!("Found some dead code");
    }

    Ok(non_reachable)
}

// Ensure that there are no unproductive cycles

fn check_productivity(
    defined_terms: &HashSet<Term>,
    term_to_terminal_map: &HashMap<Term, HashSet<Term>>,
    term_to_non_terminal_map: &HashMap<Term, HashSet<Term>>,
) -> Result<()> {
    let mut productive: HashSet<Term> = HashSet::new();

    for (term, terminal_set) in term_to_terminal_map.iter() {
        // Mark all terminal terms as productive
        if !terminal_set.is_empty() {
            productive.insert(term.clone());
        }
    }

    loop {
        let num_productive = productive.len();

        for term in defined_terms {
            // If the term is already productive continue
            if productive.contains(term) {
                continue;
            }

            if !term_to_terminal_map.get(term).unwrap().is_empty() {
                // If the term has atleast one terminal,
                // mark it as productive and continue
                productive.insert(term.clone());
                continue;
            }

            // Get all non_terminals referenced by the term

            let non_terminals = term_to_non_terminal_map.get(term).unwrap();

            let all_present = non_terminals
                .iter()
                .all(|non_terminal| productive.contains(non_terminal));

            if all_present {
                productive.insert(term.clone());
            }

            // This below check marks a non terminal as productive if it has atleast one productive
            // non terminal the above check is stricter.
            // for non_terminal in non_terminals {
            //     // If the term has atleast one productive non-terminal, mark it as productive and
            //     // continue.
            //     if productive.contains(non_terminal) {
            //         productive.insert(term.clone());
            //         continue;
            //     }
            // }
        }

        if num_productive == productive.len() {
            break;
        }
    }

    let non_productive: Vec<Term> = defined_terms.difference(&productive).cloned().collect();

    if !non_productive.is_empty() {
        let err = Report::new(GrammarError::NonProductive(non_productive));
        return Err(err);
    }

    Ok(())
}

pub fn check_correctness_and_optimize(grammar: &mut Grammar) -> Result<()> {
    grammar.get_terminal_terms();
    grammar.get_non_terminal_terms();
    let mut defined_terms = check_completeness(grammar)?;

    let transitive_closures = get_transitive_closures(grammar);

    remove_unit_productions(grammar, transitive_closures);

    grammar.get_terminal_terms();
    grammar.get_non_terminal_terms();

    let mut term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();
    let mut term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

    for term in defined_terms.iter() {
        let production = grammar.find_production(term).unwrap();
        term_to_non_terminal_map
            .entry(term.clone())
            .or_default()
            .extend(production.get_non_terminal_set().clone());
        term_to_terminal_map
            .entry(term.clone())
            .or_default()
            .extend(production.get_terminal_set().clone());
    }

    let unused_terms = check_reachability(
        grammar.get_goal(),
        &defined_terms,
        &term_to_non_terminal_map,
    )?;

    grammar.remove_definition(&unused_terms);

    for term in unused_terms {
        defined_terms.remove(&term);
        term_to_non_terminal_map.remove(&term);
        term_to_terminal_map.remove(&term);
    }

    check_productivity(
        &defined_terms,
        &term_to_terminal_map,
        &term_to_non_terminal_map,
    )?;

    Ok(())
}

fn remove_unit_productions(
    grammar: &mut Grammar,
    transitive_closure_map: HashMap<Term, HashSet<Term>>,
) {
    // For each pair in the transitive closure, add the non unit productions, remove the unit
    // productions

    for (key, closure_set) in transitive_closure_map {
        for nt in closure_set {
            // Skip the production non terminal itself
            if nt == key {
                continue;
            }
            if let Some(nt_production) = grammar.find_production(&nt) {
                // Get the non unit productions of nt
                let non_unit_productions = nt_production.get_non_unit_productions();

                if let Some(key_production) = grammar.find_production_mut(&key) {
                    // Remove unit production nt from key
                    key_production.remove_production(nt);
                    // Add the non unit productions of nt into key
                    key_production.add_production(non_unit_productions);
                }
            }
        }
    }
}

fn get_transitive_closures(grammar: &Grammar) -> HashMap<Term, HashSet<Term>> {
    let mut transitive_closures: HashMap<Term, HashSet<Term>> = HashMap::new();

    let mut queue: VecDeque<Term> = VecDeque::new();

    // Create a trivial map where each term derives itself
    // Get the transitive closure with BFS using the set value as a visited set

    for production in grammar.get_productions() {
        let left_non_terminal = production.get_left_term();
        let mut value_set: HashSet<Term> = HashSet::from([left_non_terminal.clone()]);
        queue.push_back(left_non_terminal.clone()); // Insert the element into the queue

        // Start BFS

        while !queue.is_empty() {
            let front = queue.pop_front().unwrap(); // Get element at front of queue
            let prod = grammar // Get productions of front of queue
                .get_productions()
                .iter()
                .find(|p| p.get_left_term().clone() == front)
                .unwrap();
            let unit_non_terminals = prod.get_unit_non_terminals(); // Get unit non terminals of
            // the above production

            // If these unit non terminals are not already in the value set add them, also add to
            // the queue.

            unit_non_terminals.iter().for_each(|nt| {
                if !value_set.contains(nt) {
                    queue.push_back(nt.clone());
                    value_set.insert(nt.clone());
                }
            });
        }

        transitive_closures.insert(left_non_terminal.clone(), value_set);
    }

    transitive_closures
}

#[cfg(test)]
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
        grammar::{
            GrammarError, check_productivity, check_reachability, get_transitive_closures,
            remove_unit_productions,
        },
    };

    use super::{check_completeness, grammar_tests_helper::get_token};

    #[test]
    fn test_goal_complete_reachability_successful() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\"a\"", "TERMINAL_LITERAL"),
            get_token("<nt2>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<nt2>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("B", "TERMINAL_CATEGORY"),
            get_token(";", "TERMINATION"),
        ];

        let result = ebnf::parse_grammar(tokens);

        assert!(result.is_ok());

        let mut grammar = result.unwrap();

        grammar.get_terminal_terms();
        grammar.get_non_terminal_terms();

        let defined_terms = check_completeness(&grammar);

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

        expected_term_to_non_terminal_map
            .insert(Term::NonTerminal("nt2".to_string()), HashSet::new());

        let mut expected_term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalLiteral("\"a\"".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("test".to_string()), expected_terminal_set);

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalCategory("B".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("nt2".to_string()), expected_terminal_set);

        //expected_term_to_terminal_map.insert(Term::NonTerminal("".to_string()), HashSet::new());

        let mut term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();
        let mut term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        for term in defined_terms.iter() {
            let production = grammar.find_production(term).unwrap();
            term_to_non_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_non_terminal_set().clone());
            term_to_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_terminal_set().clone());
        }

        assert_eq!(term_to_terminal_map, expected_term_to_terminal_map);
        assert_eq!(term_to_non_terminal_map, expected_term_to_non_terminal_map);

        let result = check_reachability(
            grammar.get_goal(),
            &defined_terms,
            &term_to_non_terminal_map,
        );

        assert!(result.is_ok());

        let result = result.unwrap();

        assert!(result.is_empty());

        let result = check_productivity(
            &defined_terms,
            &term_to_terminal_map,
            &term_to_non_terminal_map,
        );

        assert!(result.is_ok());
    }

    #[test]
    fn test_complete_unsuccessful() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\"a\"", "TERMINAL_LITERAL"),
            get_token("<nt2>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
        ];

        let grammar = ebnf::parse_grammar(tokens);

        assert!(grammar.is_ok());

        let mut grammar = grammar.unwrap();
        grammar.get_terminal_terms();
        grammar.get_non_terminal_terms();

        let result = check_completeness(&grammar);

        assert!(result.is_err());

        let result = result.unwrap_err();

        match result.downcast().unwrap() {
            GrammarError::ProductionNotDefined(_) => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_reachability_unsuccessful() {
        let tokens: Vec<Token> = vec![
            get_token("<test>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\"a\"", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
            get_token("<nt2>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("B", "TERMINAL_CATEGORY"),
            get_token(";", "TERMINATION"),
        ];

        let result = ebnf::parse_grammar(tokens);

        assert!(result.is_ok());

        let mut grammar = result.unwrap();

        grammar.get_terminal_terms();
        grammar.get_non_terminal_terms();

        let defined_terms = check_completeness(&grammar);

        assert!(defined_terms.is_ok());

        let defined_terms = defined_terms.unwrap();

        let mut expected_result: HashSet<Term> = HashSet::new();

        expected_result.insert(Term::NonTerminal("test".to_string()));
        expected_result.insert(Term::NonTerminal("nt2".to_string()));

        assert_eq!(defined_terms, expected_result);

        let mut expected_term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalLiteral("\"a\"".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("test".to_string()), expected_terminal_set);

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalCategory("B".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("nt2".to_string()), expected_terminal_set);

        let expected_non_terminal_set: HashSet<Term> = HashSet::new();

        let mut expected_term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        expected_term_to_non_terminal_map.insert(
            Term::NonTerminal("test".to_string()),
            expected_non_terminal_set.clone(),
        );

        expected_term_to_non_terminal_map.insert(
            Term::NonTerminal("nt2".to_string()),
            expected_non_terminal_set,
        );

        let mut term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();
        let mut term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        for term in defined_terms.iter() {
            let production = grammar.find_production(term).unwrap();
            term_to_non_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_non_terminal_set().clone());
            term_to_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_terminal_set().clone());
        }

        assert_eq!(term_to_terminal_map, expected_term_to_terminal_map);
        assert_eq!(term_to_non_terminal_map, expected_term_to_non_terminal_map);

        let result = check_reachability(
            grammar.get_goal(),
            &defined_terms,
            &term_to_non_terminal_map,
        );

        assert!(result.is_ok());

        let result = result.unwrap();

        assert!(result.len() == 1);

        assert!(*result.first().unwrap() == Term::NonTerminal("nt2".to_string()));

        let result = check_productivity(
            &defined_terms,
            &term_to_terminal_map,
            &term_to_non_terminal_map,
        );

        assert!(result.is_ok());
    }

    #[test]
    fn test_productivity_unsuccessful() {
        let tokens: Vec<Token> = vec![
            get_token("<A>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<B>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<C>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<C>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<A>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
        ];

        let grammar = ebnf::parse_grammar(tokens);

        assert!(grammar.is_ok());

        let mut grammar = grammar.unwrap();

        grammar.get_terminal_terms();
        grammar.get_non_terminal_terms();

        let mut term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();
        let mut term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        let defined_terms = check_completeness(&grammar);

        assert!(defined_terms.is_ok());

        let defined_terms = defined_terms.unwrap();

        for term in defined_terms.iter() {
            let production = grammar.find_production(term).unwrap();
            term_to_non_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_non_terminal_set().clone());
            term_to_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_terminal_set().clone());
        }

        let mut expected_result: HashSet<Term> = HashSet::new();

        expected_result.insert(Term::NonTerminal("A".to_string()));
        expected_result.insert(Term::NonTerminal("B".to_string()));
        expected_result.insert(Term::NonTerminal("C".to_string()));

        let result = check_productivity(
            &defined_terms,
            &term_to_terminal_map,
            &term_to_non_terminal_map,
        );

        assert!(result.is_err(), "Expected error, but got {:?}", result);

        let result = result.unwrap_err();

        match result.downcast_ref().unwrap() {
            GrammarError::NonProductive(_) => {}
            _ => unreachable!(),
        }
    }

    #[test]
    fn test_transitive_closure() {
        let tokens: Vec<Token> = vec![
            get_token("<S>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<A>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("\"a\"", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
            get_token("<A>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("\"b\"", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<C>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("\"c\"", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
            get_token("<C>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<S>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("\"a\"", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
        ];

        let grammar = ebnf::parse_grammar(tokens);

        assert!(grammar.is_ok());

        let grammar = grammar.unwrap();

        let transitive_closure_map = get_transitive_closures(&grammar);

        let expected_map = HashMap::from([
            (
                Term::NonTerminal("S".to_string()),
                HashSet::from([
                    Term::NonTerminal("S".to_string()),
                    Term::NonTerminal("A".to_string()),
                    Term::NonTerminal("B".to_string()),
                    Term::NonTerminal("C".to_string()),
                ]),
            ),
            (
                Term::NonTerminal("A".to_string()),
                HashSet::from([
                    Term::NonTerminal("S".to_string()),
                    Term::NonTerminal("A".to_string()),
                    Term::NonTerminal("B".to_string()),
                    Term::NonTerminal("C".to_string()),
                ]),
            ),
            (
                Term::NonTerminal("B".to_string()),
                HashSet::from([
                    Term::NonTerminal("S".to_string()),
                    Term::NonTerminal("A".to_string()),
                    Term::NonTerminal("B".to_string()),
                    Term::NonTerminal("C".to_string()),
                ]),
            ),
            (
                Term::NonTerminal("C".to_string()),
                HashSet::from([
                    Term::NonTerminal("S".to_string()),
                    Term::NonTerminal("A".to_string()),
                    Term::NonTerminal("B".to_string()),
                    Term::NonTerminal("C".to_string()),
                ]),
            ),
        ]);

        assert_eq!(
            transitive_closure_map, expected_map,
            "Expected {:?} but got {:?}",
            expected_map, transitive_closure_map
        );
    }

    #[test]
    fn test_unit_production_removal() {
        let tokens: Vec<Token> = vec![
            get_token("<S>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<A>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("0", "TERMINAL_LITERAL"),
            get_token("<X>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<A>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("1", "TERMINAL_LITERAL"),
            get_token("|", "ALTERNATION"),
            get_token("<X>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<X>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("0", "TERMINAL_LITERAL"),
            get_token("<S>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("00", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
        ];

        let result = ebnf::parse_grammar(tokens);

        assert!(result.is_ok());

        let mut grammar = result.unwrap();

        grammar.get_terminal_terms();
        grammar.get_non_terminal_terms();

        let defined_terms = check_completeness(&grammar);

        assert!(defined_terms.is_ok());

        let defined_terms = defined_terms.unwrap();

        let mut expected_result: HashSet<Term> = HashSet::new();

        expected_result.insert(Term::NonTerminal("S".to_string()));
        expected_result.insert(Term::NonTerminal("A".to_string()));
        expected_result.insert(Term::NonTerminal("X".to_string()));

        assert_eq!(defined_terms, expected_result);

        let mut expected_non_terminal_set: HashSet<Term> = HashSet::new();
        expected_non_terminal_set.insert(Term::NonTerminal("A".to_string()));
        expected_non_terminal_set.insert(Term::NonTerminal("X".to_string()));

        let mut expected_term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        expected_term_to_non_terminal_map.insert(
            Term::NonTerminal("S".to_string()),
            expected_non_terminal_set,
        );

        let mut expected_non_terminal_set = HashSet::new();

        expected_non_terminal_set.insert(Term::NonTerminal("X".to_string()));

        expected_term_to_non_terminal_map.insert(
            Term::NonTerminal("A".to_string()),
            expected_non_terminal_set,
        );

        let mut expected_non_terminal_set = HashSet::new();

        expected_non_terminal_set.insert(Term::NonTerminal("S".to_string()));

        expected_term_to_non_terminal_map.insert(
            Term::NonTerminal("X".to_string()),
            expected_non_terminal_set,
        );

        let mut expected_term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalLiteral("0".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("S".to_string()), expected_terminal_set);

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalLiteral("1".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("A".to_string()), expected_terminal_set);

        let mut expected_terminal_set = HashSet::new();

        expected_terminal_set.insert(Term::TerminalLiteral("0".to_string()));
        expected_terminal_set.insert(Term::TerminalLiteral("00".to_string()));

        expected_term_to_terminal_map
            .insert(Term::NonTerminal("X".to_string()), expected_terminal_set);

        let mut term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();
        let mut term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        for term in defined_terms.iter() {
            let production = grammar.find_production(term).unwrap();
            term_to_non_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_non_terminal_set().clone());
            term_to_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_terminal_set().clone());
        }

        assert_eq!(term_to_terminal_map, expected_term_to_terminal_map);
        assert_eq!(term_to_non_terminal_map, expected_term_to_non_terminal_map);

        let transitive_closure_map = get_transitive_closures(&grammar);

        let mut expected_transitive_closure_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        expected_transitive_closure_map.insert(
            Term::NonTerminal("S".to_string()),
            HashSet::from([
                Term::NonTerminal("S".to_string()),
                Term::NonTerminal("A".to_string()),
                Term::NonTerminal("X".to_string()),
            ]),
        );

        expected_transitive_closure_map.insert(
            Term::NonTerminal("A".to_string()),
            HashSet::from([
                Term::NonTerminal("A".to_string()),
                Term::NonTerminal("X".to_string()),
            ]),
        );

        expected_transitive_closure_map.insert(
            Term::NonTerminal("X".to_string()),
            HashSet::from([Term::NonTerminal("X".to_string())]),
        );

        assert_eq!(transitive_closure_map, expected_transitive_closure_map);

        remove_unit_productions(&mut grammar, transitive_closure_map);

        grammar.get_terminal_terms();
        grammar.get_non_terminal_terms();

        let mut term_to_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();
        let mut term_to_non_terminal_map: HashMap<Term, HashSet<Term>> = HashMap::new();

        for term in defined_terms.iter() {
            let production = grammar.find_production(term).unwrap();
            term_to_non_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_non_terminal_set().clone());
            term_to_terminal_map
                .entry(term.clone())
                .or_default()
                .extend(production.get_terminal_set().clone());
        }

        let result = check_reachability(
            grammar.get_goal(),
            &defined_terms,
            &term_to_non_terminal_map,
        );

        assert!(result.is_ok());

        let unused_terms = result.unwrap();

        grammar.remove_definition(&unused_terms);

        let tokens: Vec<Token> = vec![
            get_token("<S>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("1", "TERMINAL_LITERAL"),
            get_token("|", "ALTERNATION"),
            get_token("0", "TERMINAL_LITERAL"),
            get_token("<X>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("00", "TERMINAL_LITERAL"),
            get_token("|", "ALTERNATION"),
            get_token("0", "TERMINAL_LITERAL"),
            get_token("<S>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<X>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("0", "TERMINAL_LITERAL"),
            get_token("<S>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("00", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
        ];

        let result = ebnf::parse_grammar(tokens);

        assert!(result.is_ok());

        let mut expected_grammar = result.unwrap();

        expected_grammar.get_terminal_terms();
        expected_grammar.get_non_terminal_terms();

        assert_eq!(
            grammar, expected_grammar,
            "Expected\n{}, got\n{}",
            expected_grammar, grammar
        );
    }
}

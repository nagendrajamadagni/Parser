use std::cmp::Ordering;

use crate::ebnf::Expression;
pub use crate::ebnf::{Grammar, Production, Term};
use eyre::{Report, Result};

#[derive(Debug)]
pub enum GrammarError {
    IncompleteGrammarError(String),
    InvalidGoalError,
    ProductionNotDefinedError(Term),
}

impl std::fmt::Display for GrammarError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IncompleteGrammarError(production) => write!(
                f,
                "Error: Incomplete grammar found, cannot find any expressions for the production {production}"
            ),
            Self::InvalidGoalError => write!(
                f,
                "Error: Invalid goal term found! Goal term should be a non-terminal with valid productions"
            ),
            Self::ProductionNotDefinedError(term) => {
                write!(f, "Error: Undefined term {:?} encountered", term)
            }
        }
    }
}

impl std::error::Error for GrammarError {}

// Get list of non terminals in rhs of a grammar
fn get_rhs_non_terminals(grammar: &Grammar) -> Vec<Term> {
    let mut non_terminals = Vec::new();

    for production in grammar.get_productions() {
        for expression in production.get_expressions() {
            get_non_terminals_from_expression(expression, &mut non_terminals);
        }
    }
    non_terminals.sort();
    non_terminals.dedup();
    return non_terminals;
}

// Get list of non terminals from an expression
fn get_non_terminals_from_expression(expression: &Expression, non_terminals: &mut Vec<Term>) {
    for term in expression.get_terms() {
        get_non_terminals_from_term(term, non_terminals);
    }
}

// Get list of non terminals from a term
fn get_non_terminals_from_term(term: &Term, non_terminals: &mut Vec<Term>) {
    match term {
        Term::NonTerminal(_) => non_terminals.push(term.clone()),
        Term::Group(terms) => {
            for inner_term in terms.iter() {
                get_non_terminals_from_term(inner_term, non_terminals);
            }
        }
        Term::Repetition(term, _) => {
            get_non_terminals_from_term(term, non_terminals);
        }
        _ => {}
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
        let err = Report::new(GrammarError::IncompleteGrammarError(term_name.to_string()));
        return Err(err);
    }

    return Ok(());
}

// Check if the goal term is defined and has atleast one production rule
fn check_goal(grammar: &Grammar) -> Result<()> {
    let goal = grammar.get_goal();

    let left_term = goal.get_left_term(); // Get left term

    match left_term {
        // If the left hand of the goal is not a non-terminal return
        // an error, if it is check if it has atleast one production
        Term::NonTerminal(_) => check_non_terminal_productions(goal),
        _ => {
            let err = Report::new(GrammarError::InvalidGoalError);
            return Err(err);
        }
    }
}

// Check if all left hand non-terminal terms have atleast one production term
fn check_lhs_non_terminals(grammar: &Grammar) -> Result<Vec<Term>> {
    let mut complete_left_productions = Vec::new();

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
            Ok(()) => complete_left_productions.push(production.get_left_term().clone()),
            Err(err) => return Err(err),
        }
    }

    complete_left_productions.sort();
    complete_left_productions.dedup();

    return Ok(complete_left_productions);
}

fn check_rhs_non_terminals(grammar: &Grammar) -> Result<()> {
    let used_rhs_non_terminals = get_rhs_non_terminals(grammar);

    let defined_lhs_non_terminals = check_lhs_non_terminals(grammar)?;

    let (mut used_idx, mut defined_idx) = (0, 0);

    while used_idx < used_rhs_non_terminals.len() && defined_idx < defined_lhs_non_terminals.len() {
        // While i < list1.len and j < list2.len
        let used = &used_rhs_non_terminals[used_idx];
        let defined = &defined_lhs_non_terminals[defined_idx];

        match used.cmp(defined) {
            Ordering::Less => {
                let err = Report::new(GrammarError::ProductionNotDefinedError(used.clone()));
                return Err(err);
            } // There exists a production which is not defined
            Ordering::Equal => {
                used_idx = used_idx + 1;
                defined_idx = defined_idx + 1;
            } // Advance both pointers
            Ordering::Greater => {
                defined_idx = defined_idx + 1;
            } // There may be some unused productions which come before our
              // definition, so only advance the defined productions
        }
    }

    if used_idx == used_rhs_non_terminals.len() {
        // If we checked all the used terms return true
        return Ok(());
    } else {
        let err = Report::new(GrammarError::ProductionNotDefinedError(
            used_rhs_non_terminals[used_idx].clone(),
        ));
        return Err(err);
    }
}

pub fn check_correctness(grammar: &Grammar) -> Result<()> {
    check_goal(grammar)?;
    check_rhs_non_terminals(grammar)?;

    Ok(())
}

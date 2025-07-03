use crate::ebnf::Grammar;
use crate::ebnf::Term;
use eyre::Result;
use std::collections::HashMap;
use std::collections::HashSet;

fn remove_left_most_term(expression: &mut Vec<Term>) {
    let mut left_most = &mut expression[0];

    loop {
        match left_most {
            Term::TerminalLiteral(_) | Term::TerminalCategory(_) | Term::NonTerminal(_) => {
                expression.remove(0);
                return;
            }
            Term::Group(inner_expression) => {
                remove_left_most_term(inner_expression);
                if inner_expression.is_empty() {
                    expression.remove(0);
                }
                return;
            }
            Term::Repetition(inner_term, _) => left_most = inner_term,
        }
    }
}

fn get_left_most_term(expression: &[Term]) -> &Term {
    let mut left_most = &expression[0];

    loop {
        match left_most {
            Term::TerminalLiteral(_) | Term::TerminalCategory(_) | Term::NonTerminal(_) => {
                return left_most;
            }
            Term::Group(inner_expression) => {
                return get_left_most_term(inner_expression);
            }
            Term::Repetition(inner_term, _) => {
                left_most = inner_term;
            }
        }
    }
}

fn eliminate_left_recursion(grammar: &mut Grammar) {
    let productions = grammar.get_productions_mut();
    let mut previous_non_terminals: HashSet<Term> = HashSet::new();

    let mut definitions_to_be_added: HashMap<Term, Vec<Vec<Term>>> = HashMap::new();

    for production in productions.iter_mut() {
        // We have the list of all previous non terminals until this point
        // Check within each expression of pi, if the left-most term is a previously present non
        // terminal

        let pi_left_term = production.get_left_term().clone();

        if !production
            .get_non_terminal_set()
            .is_disjoint(&previous_non_terminals)
        {
            // Our current production references a previously encountered non-terminal. We may need
            // to substitute this term
            let pi_expressions = production.get_expressions_mut();
            for pi_exp in pi_expressions.iter() {
                let left_most_term = get_left_most_term(pi_exp);
                if previous_non_terminals.contains(left_most_term) {
                    // If the left-most term is a previously present non terminal, replace it with its
                    // productions
                    println!(
                        "Need to replace {} in the expression {:?}",
                        left_most_term, pi_exp
                    );
                }
            }
        }

        if production.get_non_terminal_set().contains(&pi_left_term) {
            // Recursion present, may or may not be left recursion
            let mut direct_left_recursion_present = false;
            for expression in production.get_expressions() {
                let left_most_term = get_left_most_term(expression);
                if *left_most_term == pi_left_term {
                    direct_left_recursion_present = true;
                }
            }

            if !direct_left_recursion_present {
                break;
            }

            // Direct left recursion definitely present

            // Get the mutable list of expressions for this production
            let pi_expressions = production.get_expressions_mut();
            // Get the A' term
            let prime_term_name = if let Term::NonTerminal(term_name) = &pi_left_term {
                format!("{}'", term_name)
            } else {
                unreachable!();
            };

            let prime_term = Term::NonTerminal(prime_term_name);

            // Keep the epsilon production ready

            let eps_production = vec![Term::TerminalCategory("EPSILON".to_string())];

            let mut i = 0;

            while i < pi_expressions.len() {
                let left_most_term = get_left_most_term(&pi_expressions[i]);
                if *left_most_term == pi_left_term {
                    // Left recursion detected

                    // Remove the term with left recursion
                    let mut removed_expression = pi_expressions.remove(i);
                    // Remove the left most term from that expression i.e the recursive term
                    remove_left_most_term(&mut removed_expression);
                    // Add the prime term at the end
                    removed_expression.push(prime_term.clone());

                    // If the A' term is not already set to be added insert a new entry and add the
                    // default epsilon expression. Otherwise, the rule with the epsilon production
                    // exists, just push this new expression i.e the BA' expression

                    match definitions_to_be_added.entry(prime_term.clone()) {
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            entry.insert(vec![eps_production.clone(), removed_expression]);
                        }
                        std::collections::hash_map::Entry::Occupied(entry) => {
                            entry.into_mut().push(removed_expression);
                        }
                    }
                } else {
                    // We must add prime term to the end of other terms
                    // Not a left recursive term so add the prime term
                    pi_expressions[i].push(prime_term.clone());
                    i += 1; // Only increment here because in the previous case we remove an
                    // element
                }
            }
        }

        previous_non_terminals.insert(pi_left_term);
    }

    for (term, definition) in definitions_to_be_added {
        grammar.add_definition(term, definition);
    }
}

pub fn check_ll1_compliance(grammar: &mut Grammar) -> Result<()> {
    eliminate_left_recursion(grammar);
    Ok(())
}

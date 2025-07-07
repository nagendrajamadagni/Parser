use crate::ebnf::Grammar;
use crate::ebnf::Production;
use crate::ebnf::Term;
use eyre::Result;
use std::collections::HashMap;
use std::collections::HashSet;

fn substitute_left_most_term(
    target_expression: &[Term],
    sub_production: &Production,
) -> Vec<Vec<Term>> {
    let left_most = &target_expression[0];

    let mut final_expressions: Vec<Vec<Term>> = Vec::new();

    match left_most {
        Term::TerminalLiteral(_) | Term::TerminalCategory(_) | Term::NonTerminal(_) => {
            let expression = &target_expression[1..];
            // Removed the left most term, need to append the productions
            for sub_expression in sub_production.get_expressions() {
                let mut prepend_expression = sub_expression.clone();
                prepend_expression.extend(expression.iter().cloned());
                final_expressions.push(prepend_expression);
            }
        }
        Term::Group(inner_expression) => {
            // Substitute the terms for the left most term in the inner expression
            let final_inner_expressions =
                substitute_left_most_term(inner_expression, sub_production);

            // Make the inner expression back into a group
            let mut grouped_terms: Vec<Vec<Term>> = Vec::new();
            for exp in final_inner_expressions {
                grouped_terms.push(vec![Term::Group(exp)]);
            }
            // Extend the group with the remaining terms in the target expression
            for exp in grouped_terms.iter_mut() {
                exp.extend_from_slice(&target_expression[1..]);
            }
            final_expressions.extend(grouped_terms);
        }
        Term::Repetition(inner_term, repetition_type) => {
            let final_inner_expressions =
                substitute_left_most_term(&[*inner_term.clone()], sub_production);

            // Make the inner expressions also into repetitions

            let mut repetition_expressions: Vec<Vec<Term>> = Vec::new();

            for exp in final_inner_expressions {
                let num_expressions = exp.len();
                if num_expressions > 1 {
                    repetition_expressions.push(vec![Term::Repetition(
                        Box::new(Term::Group(exp)),
                        repetition_type.clone(),
                    )]);
                } else {
                    repetition_expressions.push(vec![Term::Repetition(
                        Box::new(exp[0].clone()),
                        repetition_type.clone(),
                    )]);
                }
            }

            for exp in repetition_expressions.iter_mut() {
                exp.extend_from_slice(&target_expression[1..]);
            }

            final_expressions.extend(repetition_expressions);
        }
    }

    final_expressions
}

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
    let mut previous_non_terminals: HashSet<Term> = HashSet::new();
    let mut definitions_to_be_added: HashMap<Term, Vec<Vec<Term>>> = HashMap::new();

    let num_productions = grammar.get_productions().len();

    for idx in 0..num_productions {
        // We have the list of all previous non terminals until this point
        // Check within each expression of pi, if the left-most term is a previously present non
        // terminal

        let pi_left_term = {
            let productions = grammar.get_productions();
            productions[idx].get_left_term().clone()
        };

        let needs_substitution = {
            let productions = grammar.get_productions();
            let production = &productions[idx];
            !production
                .get_non_terminal_set()
                .is_disjoint(&previous_non_terminals)
        };

        if needs_substitution {
            // Our current production references a previously encountered non-terminal. We may need
            // to substitute this term

            let num_expressions = {
                let productions = grammar.get_productions();
                let production = &productions[idx];
                production.get_expressions().len()
            };

            for exp_idx in 0..num_expressions {
                let (needs_sub, left_most_term) = {
                    let productions = grammar.get_productions();
                    let production = &productions[idx];
                    let pi_exp = &production.get_expressions()[exp_idx];
                    let left_most_term = get_left_most_term(pi_exp);
                    let needs_sub = previous_non_terminals.contains(left_most_term);
                    (needs_sub, left_most_term.clone())
                };

                // If the left-most term is a previously present non terminal, replace it with its
                // productions
                if needs_sub {
                    // Find the production whose expressions need to be substituted in pi_exp

                    let sub_production = grammar.find_production(&left_most_term).cloned();

                    if let Some(sub_production) = sub_production {
                        // If there exists a production whose expressions we can substitute
                        let productions = grammar.get_productions_mut();
                        // This is the expression which we will be substituting the term with its
                        // expressions
                        let target_expression = productions[idx].get_expressions()[exp_idx].clone();

                        // First we remove the expression from the production

                        productions[idx].remove_expression(&target_expression);

                        // Then we create new expressions after replacing the non terminal with its
                        // expressions

                        let expressions_to_add =
                            substitute_left_most_term(&target_expression, &sub_production);

                        // Then we add all the new expressions into the production

                        productions[idx].add_expression(&expressions_to_add);
                    }
                }
            }
        }

        let production = &mut grammar.get_productions_mut()[idx];

        production.get_non_terminal_terms();

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

#[cfg(test)]
mod grammar_tests_helper {
    use lexviz::scanner::Token;

    pub fn get_token(token: &str, category: &str) -> Token {
        Token::new(token.to_string(), category.to_string())
    }
}

#[cfg(test)]
mod ll_parser_test {
    use std::collections::HashSet;

    use lexviz::scanner::Token;

    use crate::{
        cfg::{Term, check_correctness_and_optimize},
        ebnf::parse_grammar,
        ll::eliminate_left_recursion,
    };

    use super::grammar_tests_helper::get_token;

    #[test]
    fn test_left_recursion_elimination() {
        let tokens: Vec<Token> = vec![
            get_token("<A>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\"(\"", "TERMINAL_LITERAL"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("\")\"", "TERMINAL_LITERAL"),
            get_token("\"+\"", "TERMINAL_LITERAL"),
            get_token("<C>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<C>", "NON_TERMINAL"),
            get_token("\"abc\"", "TERMINAL_LITERAL"),
            get_token("|", "ALTERNATION"),
            get_token("(", "LPAREN"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("\"h\"", "TERMINAL_LITERAL"),
            get_token(")", "RPAREN"),
            get_token("+", "PLUS"),
            get_token("\"f\"", "TERMINAL_LITERAL"),
            get_token("|", "ALTERNATION"),
            get_token("\"g\"", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
            get_token("<C>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("(", "LPAREN"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("\"i\"", "TERMINAL_LITERAL"),
            get_token(")", "RPAREN"),
            get_token("+", "QUESTION"),
            get_token("\"d\"", "TERMINAL_LITERAL"),
            get_token("|", "ALTERNATION"),
            get_token("\"e\"", "TERMINAL_LITERAL"),
            get_token(";", "TERMINATION"),
        ];

        let result = parse_grammar(tokens);

        assert!(result.is_ok());

        let mut grammar = result.unwrap();

        let result = check_correctness_and_optimize(&mut grammar);

        assert!(result.is_ok());

        eliminate_left_recursion(&mut grammar);

        let tokens: Vec<Token> = vec![
            get_token("<A>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("\"(\"", "TERMINAL_LITERAL"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("\")\"", "TERMINAL_LITERAL"),
            get_token("\"+\"", "TERMINAL_LITERAL"),
            get_token("<C>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<B>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("<C>", "NON_TERMINAL"),
            get_token("\"abc\"", "TERMINAL_LITERAL"),
            get_token("<B'>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("\"g\"", "TERMINAL_LITERAL"),
            get_token("<B'>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<C>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("(", "LPAREN"),
            get_token("\"g\"", "TERMINAL_LITERAL"),
            get_token("<B'>", "NON_TERMINAL"),
            get_token("\"i\"", "TERMINAL_LITERAL"),
            get_token(")", "RPAREN"),
            get_token("?", "QUESTION"),
            get_token("\"d\"", "TERMINAL_LITERAL"),
            get_token("<C'>", "NON_TERMINAL"),
            get_token("|", "ALTERNATION"),
            get_token("\"e\"", "TERMINAL_LITERAL"),
            get_token("<C'>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<B'>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("EPSILON", "TERMINAL_CATEGORY"),
            get_token("|", "ALTERNATION"),
            get_token("(", "LPAREN"),
            get_token("\"h\"", "TERMINAL_LITERAL"),
            get_token(")", "RPAREN"),
            get_token("+", "PLUS"),
            get_token("\"f\"", "TERMINAL_LITERAL"),
            get_token("<B'>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
            get_token("<C'>", "NON_TERMINAL"),
            get_token("::=", "DEFINES"),
            get_token("EPSILON", "TERMINAL_CATEGORY"),
            get_token("|", "ALTERNATION"),
            get_token("(", "LPAREN"),
            get_token("\"abc\"", "TERMINAL_LITERAL"),
            get_token("<B'>", "NON_TERMINAL"),
            get_token("\"i\"", "TERMINAL_LITERAL"),
            get_token(")", "RPAREN"),
            get_token("?", "QUESTION"),
            get_token("\"d\"", "TERMINAL_LITERAL"),
            get_token("<C'>", "NON_TERMINAL"),
            get_token(";", "TERMINATION"),
        ];

        let result = parse_grammar(tokens);

        assert!(result.is_ok(), "Expected ok result but got {:?}", result);

        let mut expected_grammar = result.unwrap();

        let result = check_correctness_and_optimize(&mut expected_grammar);

        assert!(result.is_ok());

        for production in expected_grammar.get_productions() {
            let left_term = production.get_left_term();
            let test_production = grammar.find_production(left_term);
            assert!(test_production.is_some());
            let test_production = test_production.unwrap();
            let expressions = production.get_expressions();
            let test_expressions = test_production.get_expressions();
            let expression_set: HashSet<Vec<Term>> = expressions.iter().cloned().collect();
            let test_expression_set: HashSet<Vec<Term>> =
                test_expressions.iter().cloned().collect();

            assert_eq!(
                expression_set, test_expression_set,
                "Expected {:?} but got {:?} for production {:?}",
                expression_set, test_expression_set, left_term
            );
        }
    }
}

use cfg::check_correctness_and_optimize;
use lexviz::{
    construct_dfa, construct_minimal_dfa, construct_nfa, construct_scanner, parse_microsyntax_list,
};

mod cfg;
mod ebnf;
mod ll;

use color_eyre::eyre::Result;
use ll::check_ll1_compliance;

fn get_ebnf_mst_list() -> Vec<(String, String)> {
    let ebnf_mst_list: Vec<(String, String)> = vec![
        ("<[A-Za-z0-9-]+>".to_string(), "NON_TERMINAL".to_string()),
        (
            "\"[A-Za-z0-9-:'!+<>=*()]+\"".to_string(),
            "TERMINAL_LITERAL".to_string(),
        ),
        ("[A-Z]+".to_string(), "TERMINAL_CATEGORY".to_string()),
        ("::=".to_string(), "DEFINES".to_string()),
        ("\\|".to_string(), "ALTERNATION".to_string()),
        ("\\*".to_string(), "ASTERISK".to_string()),
        ("\\+".to_string(), "PLUS".to_string()),
        ("\\?".to_string(), "QUESTION".to_string()),
        ("\\(".to_string(), "LPAREN".to_string()),
        ("\\)".to_string(), "RPAREN".to_string()),
        (";".to_string(), "TERMINATION".to_string()),
        ("[ \n\t\r]+".to_string(), "WHITESPACE".to_string()),
    ];

    ebnf_mst_list
}

fn main() -> Result<()> {
    color_eyre::install()?;
    let ebnf_mst_list = get_ebnf_mst_list();

    let diamondback_ebnf = "left_recursion.ebnf".to_string();

    let syntax_tree_list = parse_microsyntax_list(ebnf_mst_list).unwrap();

    let nfa = construct_nfa(syntax_tree_list, false).unwrap();

    let dfa = construct_dfa(&nfa, false);

    let minimal_dfa = construct_minimal_dfa(&dfa, false);

    let scanner = construct_scanner(&minimal_dfa);

    let lexed_output = scanner
        .scan(
            diamondback_ebnf,
            None,
            false,
            Some(vec!["WHITESPACE".to_string()]),
        )
        .unwrap();

    let mut grammar = ebnf::parse_grammar(lexed_output).unwrap();

    check_correctness_and_optimize(&mut grammar)?;

    check_ll1_compliance(&mut grammar)?;

    println!("The grammar after optimization is\n{}", grammar);

    Ok(())
}

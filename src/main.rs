use lexviz::{
    construct_dfa, construct_minimal_dfa, construct_nfa, construct_scanner, parse_microsyntax_list,
};

mod ebnf;

fn get_ebnf_mst_list() -> Vec<(String, String)> {
    let mut ebnf_mst_list: Vec<(String, String)> = Vec::new();

    ebnf_mst_list.push(("<[A-Za-z0-9-]+>".to_string(), "NON_TERMINAL".to_string()));
    ebnf_mst_list.push((
        "\"[A-Za-z0-9-:'!+<>=*()]+\"".to_string(),
        "TERMINAL".to_string(),
    ));
    ebnf_mst_list.push(("::=".to_string(), "DEFINES".to_string()));
    ebnf_mst_list.push(("\\|".to_string(), "ALTERNATION".to_string()));
    ebnf_mst_list.push(("\\*".to_string(), "ASTERISK".to_string()));
    ebnf_mst_list.push(("\\+".to_string(), "PLUS".to_string()));
    ebnf_mst_list.push(("\\?".to_string(), "QUESTION".to_string()));
    ebnf_mst_list.push(("\\(".to_string(), "LPAREN".to_string()));
    ebnf_mst_list.push(("\\)".to_string(), "RPAREN".to_string()));
    ebnf_mst_list.push((";".to_string(), "TERMINATION".to_string()));

    return ebnf_mst_list;
}

fn main() {
    let ebnf_mst_list = get_ebnf_mst_list();

    let diamondback_ebnf = "diamondback.ebnf".to_string();

    let syntax_tree_list = parse_microsyntax_list(ebnf_mst_list).unwrap();

    let nfa = construct_nfa(syntax_tree_list, false).unwrap();

    let dfa = construct_dfa(&nfa, false);

    let minimal_dfa = construct_minimal_dfa(&dfa, false);

    let scanner = construct_scanner(&minimal_dfa);

    let lexed_output = scanner.scan(diamondback_ebnf, None, true, None).unwrap();

    let diamondback_grammar = ebnf::parse_grammar(lexed_output).unwrap();
}

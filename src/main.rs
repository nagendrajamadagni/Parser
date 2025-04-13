mod ebnf;

fn main() {
    let file_path = "diamondback.lex";
    let diamondback_grammar = ebnf::parse_grammar(file_path);
}

extern crate lalrpop;
fn main() {
    println!("Running build...");
    lalrpop::Configuration::new()
        .log_verbose()
        .process_file("src/lang.lalrpop").unwrap();

    println!("Done building");
}

#![feature(nll)]

extern crate chrono;
extern crate clap;
extern crate lalrpop_util;
extern crate libc;
extern crate procfs;
extern crate regex;

#[macro_use]
extern crate lazy_static;

use procfs::{Meminfo, ProcResult, Process};

use clap::{App, Arg};
use regex::Regex;

mod ast;
pub mod lang;
mod lexer;
mod util;

lazy_static! {
    pub static ref BYTES_REGEX: Regex =
        { Regex::new(r"^(\d+)((?:[kKMG]i?)?B)?$").expect("Failed to compile bytes regex") };
    pub static ref DURATION_REGEX: Regex =
        { Regex::new(r"^(\d+)([a-z]+)$").expect("Failed to compile duration regex") };
    pub static ref MEMINFO: Meminfo = { Meminfo::new().unwrap() };
}

#[cfg(test)]
fn parse(
    s: &str,
) -> Result<ast::RawClause, lalrpop_util::ParseError<usize, lexer::Token, lexer::LexicalError>> {
    let l = lexer::Lexer::new(s);
    let p = lang::RawClauseParser::new();
    p.parse(l)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::{Op, RawClause};
    use std::cmp::PartialEq;
    use std::fmt::Debug;

    fn expect_expr<A, O, B>(expr: &RawClause, a: A, o: O, b: B)
    where
        A: Debug,
        String: PartialEq<A>,
        O: Debug,
        Op: PartialEq<O>,
        B: Debug,
        String: PartialEq<B>,
    {
        match expr {
            &RawClause::Expr(ref aa, ref oo, ref bb) => {
                assert_eq!(aa, &a);
                assert_eq!(oo, &o);
                assert_eq!(bb, &b);
            }
            expr => panic!(
                "Unable to match the following clause as an expression:\n{:?}",
                expr
            ),
        }
    }

    /// Tests all of the different operators
    #[test]
    fn test_simple_parsing() {
        let expr = parse("a == b").unwrap();
        expect_expr(&expr, "a", Op::Equals, "b");

        let expr = parse("a != b").unwrap();
        expect_expr(&expr, "a", Op::NotEquals, "b");

        let expr = parse("a > b").unwrap();
        expect_expr(&expr, "a", Op::GreaterThan, "b");

        let expr = parse("a >= b").unwrap();
        expect_expr(&expr, "a", Op::GreaterThanEq, "b");

        let expr = parse("a < b").unwrap();
        expect_expr(&expr, "a", Op::LessThan, "b");

        let expr = parse("a <= b").unwrap();
        expect_expr(&expr, "a", Op::LessThanEq, "b");

        let expr = parse("a like b").unwrap();
        expect_expr(&expr, "a", Op::Like, "b");
    }

    /// Tests nested clauses
    #[test]
    fn test_nested_clauses() {
        let expr = parse("a == b and c > 4").unwrap();
        println!("{:?}", expr);
        match expr {
            RawClause::And(left, right) => {
                expect_expr(&*left, "a", Op::Equals, "b");
                expect_expr(&*right, "c", Op::GreaterThan, "4");
            }
            _ => panic!("Did not parse into an And clause"),
        }

        let expr = parse("a == b or c > 4").unwrap();
        println!("{:?}", expr);
        match expr {
            RawClause::Or(left, right) => {
                expect_expr(&*left, "a", Op::Equals, "b");
                expect_expr(&*right, "c", Op::GreaterThan, "4");
            }
            _ => panic!("Did not parse into an And clause"),
        }

        let expr = parse("a == a and (b == b or c == c)").unwrap();
        println!("{:?}", expr);
        match expr {
            RawClause::And(ref a, ref right) => {
                expect_expr(&*a, "a", Op::Equals, "a");

                match **right {
                    RawClause::Or(ref b, ref c) => {
                        expect_expr(&*b, "b", Op::Equals, "b");
                        expect_expr(&*c, "c", Op::Equals, "c");
                    }
                    _ => panic!("Did not parse into an Or clause"),
                }
            }
            _ => panic!("Did not parse into an And clause"),
        }
    }

    #[test]
    fn test_check() {
        //let p = lang::RawClauseParser::new();

        //let raw = p.parse(&mut _errors, "comm eq 'java' and pid != 1").unwrap();
        //let check = raw.check();

        //println!("{:?}", check);
    }

    #[test]
    fn test_realproc() {
        //let myself = procfs::Proc::myself().unwrap();
        //let p = lang::RawClauseParser::new();

        //let raw = p.parse(&mut _errors, "pid == 1 or pid != 1").unwrap();
        //let check = raw.check().unwrap();
        //assert!(check.evaluate(&myself).unwrap());

        //let raw = p.parse(&mut _errors, "pid == 1 and pid != 1").unwrap();
        //let check = raw.check().unwrap();
        //assert!(!check.evaluate(&myself).unwrap());
    }
}

struct ProcFormatter<'a, 'b> {
    proc_obj: &'a Process,
    formats: &'b [&'b str],
}

impl<'a, 'b> std::fmt::Display for ProcFormatter<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for fms in self.formats.iter() {
            match *fms {
                "pid" => write!(f, "{}", self.proc_obj.stat.pid)?,
                "uid" => write!(f, "{}", self.proc_obj.owner)?,
                "owner" | "user" => write!(
                    f,
                    "{}",
                    util::lookup_username(self.proc_obj.owner)
                        .unwrap_or(format!("{}", self.proc_obj.owner))
                )?,
                "comm" => write!(f, "{}", self.proc_obj.stat.comm)?,
                "cmdline" => {
                    let cmdline = self.proc_obj.cmdline();
                    if let Ok(cmdline) = cmdline {
                        write!(f, "{}", cmdline.join(" "))?
                    } else {
                        write!(f, "?")?
                    }
                }
                "rss" => write!(f, "{}", self.proc_obj.stat.rss_bytes())?,
                "vmsize" | "vsize" => write!(f, "{}", self.proc_obj.stat.vsize)?,
                x => write!(f, "{}", x)?,
            }
            write!(f, " ")?;
        }

        Ok(())
    }
}

fn get_signal_from_name(sig: &str) -> Option<i32> {
    match sig {
        "SIGINT" | "INT" => Some(libc::SIGINT),
        "SIGKILL" | "KILL" => Some(libc::SIGKILL),
        "SIGTERM" | "TERM" => Some(libc::SIGTERM),
        "SIGHUP" | "HUP" => Some(libc::SIGHUP),
        "SIGUSR1" | "USR1" => Some(libc::SIGUSR1),
        "SIGUSR2" | "USR2" => Some(libc::SIGUSR2),
        _ => None,
    }
}

fn get_signal_from_int(sig: &str) -> Option<i32> {
    i32::from_str_radix(sig, 10).ok().and_then(|int| match int {
        | libc::SIGINT
        | libc::SIGKILL
        | libc::SIGTERM
        | libc::SIGHUP
        | libc::SIGUSR1
        | libc::SIGUSR2 => Some(int),
        _ => None,
    })
}

fn main() {
    let matches = App::new("procfind")
        .arg(
            Arg::with_name("pred")
                .takes_value(true)
                .help("Process search filter string"),
        )
        .arg(
            Arg::with_name("output")
                .short("o")
                .long("output")
                .takes_value(true)
                .help("Output format"),
        )
        .arg(
            Arg::with_name("signal")
                .long("signal")
                .takes_value(true)
                .help("Signal to send to each matching process"),
        )
        .get_matches();

    let signal: Option<i32> = matches.value_of("signal").and_then(|s| {
        let sig = get_signal_from_name(s).or_else(|| get_signal_from_int(s));
        if sig.is_none() {
            eprintln!("Warning: {} is not a recognized signal", s);
        }
        sig
    });

    let pred = if let Some(values) = matches.value_of("pred") {
        values
    } else {
        // dummy clause that will return true for everything
        "pid >= 0"
    };

    let parser = lang::RawClauseParser::new();
    let lexer = lexer::Lexer::new(&pred);
    let clause = match parser.parse(lexer) {
        Ok(raw) => match raw.check() {
            Ok(clause) => clause,
            Err(e) => {
                eprintln!("Failed to validate the find clause:");
                eprintln!("{}", e);
                std::process::exit(1);
            }
        },
        Err(e) => {
            eprintln!("Failed to parse the find clause:");
            eprintln!("{}", e);
            std::process::exit(1);
        }
    };

    let all_procs = procfs::all_processes();
    let matching = all_procs
        .iter()
        .filter(|procs| clause.evaluate(procs).unwrap());

    let fmt: Vec<&str> = if let Some(output_format) = matches.value_of("output") {
        output_format.split(',').collect()
    } else {
        vec!["pid", "comm"]
    };

    for mproc in matching {
        let fproc = ProcFormatter {
            proc_obj: &mproc,
            formats: &fmt,
        };
        println!("{}", fproc);
        if let Some(s) = signal {
            println!("Sending signal {} to pid {}", s, mproc.pid());
            unsafe { libc::kill(mproc.pid(), s) };
        }
    }
}

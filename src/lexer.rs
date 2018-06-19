use std::fmt;

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(Debug, Eq, PartialEq)]
pub enum Token {
    And,
    Or,
    LParen,
    RParen,
    //StrEq,
    //StrNeq,
    //Like,
    Equals,
    NotEquals,
    GreaterThan,
    GreaterThanEq,
    LessThan,
    LessThanEq,
    Word(String),
}

#[derive(Debug, PartialEq)]
pub enum LexicalError {
    UnmatchedQuote,
    UnexpectedEOF,
    UnexpectedChar(char),
    UnknownEscape(char),
}

impl fmt::Display for LexicalError {
    fn fmt(&self, _f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        unimplemented!()
    }
}

impl fmt::Display for Token {
    fn fmt(&self, _f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        unimplemented!()
    }
}

use std::iter::Peekable;
use std::str::CharIndices;

pub struct Lexer<'input> {
    chars: Peekable<CharIndices<'input>>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str) -> Self {
        Lexer {
            chars: input.char_indices().peekable(),
        }
    }

    // parsed until the next whitespace or end-of-stream
    fn bare_word(&mut self, start_char: char, start_pos: usize) -> (usize, Token, usize) {
        let mut s = String::new();
        s.push(start_char);
        let mut end = start_pos;
        loop {
            end += 1;
            match self.chars.peek() {
                Some((_, c)) if c.is_whitespace() => break,
                Some((_, c)) => match c {
                    '!' | '=' | '(' | ')' | '<' | '>' => break,
                    _ => s.push(self.chars.next().unwrap().1),
                },
                None => break,
            }
        }

        let token = match s {
            _ if s == "and" => Token::And,
            _ if s == "or" => Token::Or,
            other => Token::Word(other),
        };

        (start_pos, token, end)
    }

    fn expect(
        &mut self,
        start: usize,
        expect: char,
        tok: Token,
    ) -> Result<(usize, Token, usize), LexicalError> {
        match self.chars.next() {
            Some((i, c)) if c == expect => Ok((start, tok, i + 1)),
            Some((_, c)) => Err(LexicalError::UnexpectedChar(c)),
            None => Err(LexicalError::UnexpectedEOF),
        }
    }

    fn lt(&mut self, start: usize) -> (usize, Token, usize) {
        match self.chars.peek() {
            Some((_, '=')) => {
                self.chars.next();
                (start, Token::LessThanEq, start + 2)
            }
            _ => (start, Token::LessThan, start + 1),
        }
    }
    fn gt(&mut self, start: usize) -> (usize, Token, usize) {
        match self.chars.peek() {
            Some((_, '=')) => {
                self.chars.next();
                (start, Token::GreaterThanEq, start + 2)
            }
            _ => (start, Token::GreaterThan, start + 1),
        }
    }

    fn quote(&mut self, start: usize) -> Result<(usize, Token, usize), LexicalError> {
        let mut s = String::new();
        let end;
        loop {
            match self.chars.next() {
                Some((i, '"')) => {
                    end = i;
                    break;
                }
                Some((_, '\\')) => match self.chars.next() {
                    Some((_, 't')) => s.push('\t'),
                    Some((_, 'n')) => s.push('\n'),
                    Some((_, c)) => return Err(LexicalError::UnknownEscape(c)),
                    None => return Err(LexicalError::UnexpectedEOF),
                },
                Some((_, c)) => s.push(c),
                None => return Err(LexicalError::UnexpectedEOF),
            }
        }

        Ok((start, Token::Word(s), end))
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Spanned<Token, usize, LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.chars.next() {
                Some((i, '(')) => return Some(Ok((i, Token::LParen, i + 1))),
                Some((i, ')')) => return Some(Ok((i, Token::RParen, i + 1))),
                Some((i, '=')) => return Some(self.expect(i, '=', Token::Equals)),
                Some((i, '!')) => return Some(self.expect(i, '=', Token::NotEquals)),
                Some((i, '<')) => return Some(Ok(self.lt(i))),
                Some((i, '>')) => return Some(Ok(self.gt(i))),
                Some((i, '"')) => return Some(self.quote(i)),
                Some((_, c)) if c.is_whitespace() => continue, // skip whitespace
                Some((i, c)) => return Some(Ok(self.bare_word(c, i))),
                None => return None, // End of file
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unpack(v: Result<(usize, Token, usize), LexicalError>) -> Token {
        if let Ok((_, t, _)) = v {
            t
        } else {
            panic!("Unable to unpack token")
        }
    }

    #[test]
    fn test_lexer() {
        let s = "( hello==world) and comm eq \"ru\\t  st\"!= == < <= > >=";
        let mut l = Lexer::new(s);

        assert_eq!(unpack(l.next().unwrap()), Token::LParen);
        assert_eq!(unpack(l.next().unwrap()), Token::Word("hello".to_owned()));
        assert_eq!(unpack(l.next().unwrap()), Token::Equals);
        assert_eq!(unpack(l.next().unwrap()), Token::Word("world".to_owned()));
        assert_eq!(unpack(l.next().unwrap()), Token::RParen);
        assert_eq!(unpack(l.next().unwrap()), Token::And);
        assert_eq!(unpack(l.next().unwrap()), Token::Word("comm".to_owned()));
        assert_eq!(unpack(l.next().unwrap()), Token::Word("eq".to_owned()));
        assert_eq!(
            unpack(l.next().unwrap()),
            Token::Word("ru\t  st".to_owned())
        );
        assert_eq!(unpack(l.next().unwrap()), Token::NotEquals);
        assert_eq!(unpack(l.next().unwrap()), Token::Equals);
        assert_eq!(unpack(l.next().unwrap()), Token::LessThan);
        assert_eq!(unpack(l.next().unwrap()), Token::LessThanEq);
        assert_eq!(unpack(l.next().unwrap()), Token::GreaterThan);
        assert_eq!(unpack(l.next().unwrap()), Token::GreaterThanEq);
    }

    #[test]
    fn test_error_handling() {
        let mut l = Lexer::new("!");
        assert_eq!(l.next(), Some(Err(LexicalError::UnexpectedEOF)));

        let mut l = Lexer::new("\"hello");
        assert_eq!(l.next(), Some(Err(LexicalError::UnexpectedEOF)));

        let mut l = Lexer::new("\"he\\llo");
        assert_eq!(l.next(), Some(Err(LexicalError::UnknownEscape('l'))));
    }

    fn test_span(text: &str, spans: Vec<&'static str>) {
        let mut l = Lexer::new(text);
        for span in spans {
            match l.next() {
                Some(Ok((start, tok, end))) => {
                    println!("{:?}", tok);
                    println!("{}-{}", start, end);
                    println!("{}", span);
                    let len = span.len();
                    let mut span = span.chars();
                    for idx in 0..len {
                        if idx >= start && idx < end {
                            assert_eq!(span.next().unwrap(), '~');
                        } else {
                            assert_eq!(span.next().unwrap(), ' ');
                        }
                    }
                }
                x => panic!("Unexpected next: {:?}", x),
            }
        }
    }

    #[test]
    fn test_spans() {
        //                 1
        //       01234567890123
        test_span(
                "hello(==) world    blah",
            vec![
                "~~~~~                  ",
                "     ~                 ",
                "      ~~               ",
                "        ~              ",
                "          ~~~~~        ",
                "                   ~~~~",
            ],
        );
    }

}

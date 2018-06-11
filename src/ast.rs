#[cfg(test)]
extern crate libc;

use {BYTES_REGEX, MEMINFO};
use procfs::Proc;
use util;

#[derive(Debug, Eq, PartialEq)]
pub enum RawClause {
    And(Box<RawClause>, Box<RawClause>),
    Or(Box<RawClause>, Box<RawClause>),
    Expr(String, Op, String),
}

impl RawClause {
    pub fn check(self) -> Result<Clause, String> {
        match self {
            RawClause::And(a, b) => Ok(Clause::And(Box::new(a.check()?), Box::new(b.check()?))),
            RawClause::Or(a, b) => Ok(Clause::Or(Box::new(a.check()?), Box::new(b.check()?))),
            RawClause::Expr(field, op, value_str) => {
                let field = Field::from_str(&field)?;

                let value = field.build_value_from_str(&value_str)?;

                //if !field.works_with(op) {
                //    return Err(format!("Field {:?} is not compatible with operator {:?}", field, op));
                //}


                Ok(Clause::Expr(field, op, value))
            }
        }
    }
}



#[derive(Debug, PartialEq)]
pub enum Clause {
    And(Box<Clause>, Box<Clause>),
    Or(Box<Clause>, Box<Clause>),
    Expr(Field, Op, Value),
}

impl Clause {
    /// Test if a given process matches this clause
    pub fn evaluate(&self, p: &Proc) -> Result<bool, String> {
        match self {
            Clause::And(a, b) => Ok(a.evaluate(p)? && b.evaluate(p)?),
            Clause::Or(a, b) => Ok(a.evaluate(p)? || b.evaluate(p)?),
            Clause::Expr(field, op, value) => match (field, op, value) {
                (Field::Comm, op, Value::S(value)) => Ok(op.compare_str(&p.stat.comm, &value)),
                (Field::Pid, op, Value::Unitless(value)) => Ok(op.compare_numeric(p.stat.pid, *value)),
                (Field::Uid, op, Value::Unitless(uid)) => Ok(op.compare_numeric(p.owner, *uid as u32)),
                (Field::Rss, op, Value::Bytes(bytes)) => Ok(op.compare_numeric(p.stat.rss_bytes(), *bytes as i64)),
                (Field::Rss, op, Value::Percent(pct)) => Ok(op.compare_numeric(p.stat.rss_bytes(), (MEMINFO.mem_total as f64 * *pct as f64) as i64)),
                (Field::Vsize, op, Value::Bytes(bytes)) => Ok(op.compare_numeric(p.stat.vsize, *bytes as u64)),
                (Field::Vsize, op, Value::Percent(pct)) => Ok(op.compare_numeric(p.stat.vsize, (MEMINFO.mem_total as f64 * *pct as f64) as u64)),
                //(Field::Cmdline, op, Value::S(value)) if op.is_string() => Ok(op.compare_str

                _ => Err(format!("Invalid clause: {:?} {:?} {:?}", field, op, value))
            }
        }
    }
}


#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Field {
    Pid,
    Uid,
    Comm,
    Rss,
    Vsize,
    Cmdline,
    #[cfg(test)]
    A,
}

impl Field {
    fn from_str(s: &str) -> Result<Field, String> {
        match s {
            "uid" => Ok(Field::Uid),
            "comm" => Ok(Field::Comm),
            "pid" => Ok(Field::Pid),
            "rss" => Ok(Field::Rss),
            "cmdline" => Ok(Field::Cmdline),
            "vsize" | "vmsize" => Ok(Field::Vsize),
            #[cfg(test)]
            "a" | "b" | "c" => Ok(Field::A),
            _ => Err(format!("Field '{}' not recognized", s))
        }
    }


    fn build_value_from_str(&self, s: &str) -> Result<Value, String> {
        match *self {
            #[cfg(test)]
            Field::A => Ok(Value::build_string(s)),
            Field::Comm =>  Ok(Value::build_string(s)),
            Field::Pid => i32::from_str_radix(s, 10).map(Value::Unitless).map_err(|e| format!("Unable to parse as int: {:?}", e)),
            Field::Uid => {
                // if the string is parsable as an int, use that.  else try look up the provided string as a username
                i32::from_str_radix(s, 10)
                    .map(Value::Unitless)
                    .or_else(|_e| {
                        util::lookup_uid(s).map(|i| Value::Unitless(i as i32))
                    })
            }
            Field::Rss | Field::Vsize => {
                if s.ends_with('%') {
                    use std::str::FromStr;
                    let p = f32::from_str(&s[..s.len()-1]).map_err(|_| format!("Unable to parse {} as a percentage", s))?;
                    if p < 0.0 {
                        Err(format!("Percentage must be >= 0"))
                    } else if p > 100.0 {
                        Err(format!("Percentage must be <= 100"))
                    } else {
                        Ok(Value::Percent(p / 100.0))
                    }
                } else {
                BYTES_REGEX.captures(s)
                    .and_then(|caps|  {
                        Some((caps.get(1)?.as_str(), caps.get(2).map(|x| x.as_str()).unwrap_or("B")))
                    }
                    ).and_then(|(num_part, unit_part)| {
                        let num_part = i32::from_str_radix(num_part, 10).ok()?;
                        match unit_part {
                            "B" => Some(Value::Bytes(num_part)),
                            "KiB" => Some(Value::Bytes(num_part * 1024)),
                            "KB" | "kB" => Some(Value::Bytes(num_part * 1000)),
                            "MiB" => Some(Value::Bytes(num_part * 1024 * 1024)),
                            "MB" => Some(Value::Bytes(num_part * 1000 * 1000)),
                            "GiB" => Some(Value::Bytes(num_part * 1024 * 1024 * 1024)),
                            "GB" => Some(Value::Bytes(num_part * 1000 * 1000 * 1000)),
                            _ => None
                        }
                    }).ok_or(format!("Unable to parse {:?} as a data size", s))
                }


            }
            Field::Cmdline =>  Ok(Value::build_string(s)),
        }
    }
}


#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op {
    Equals,
    NotEquals,
    LessThan,
    GreaterThan,
    LessThanEq,
    GreaterThanEq,
    Like,
    Unknown(String)
}

impl Op {
    pub fn from_word(s: String) -> Op {
        if s == "like" {
            Op::Like
        } else {
            Op::Unknown(s)
        }
    }



    /// Assuming this operator is numeric, does the necessary comparison
    ///
    /// Panics if this is a string operator
    fn compare_numeric<T>(&self, a: T, b: T) -> bool
    where T: PartialEq + PartialOrd {
        match *self {
            Op::Unknown(ref s) => panic!("Called compare_numeric on an unknown operator {}", s),
            Op::Like => panic!("Called compare_numeric on a string operator"),
            Op::Equals => a == b,
            Op::NotEquals => a != b,
            Op::LessThan => a < b,
            Op::GreaterThan => a > b,
            Op::LessThanEq => a <= b,
            Op::GreaterThanEq => a >= b
        }
    }

    fn compare_str(&self, a: &str, b: &str) -> bool {
        match *self {
            Op::Unknown(ref s) => panic!("Called compare_str on an unknown operator {}", s),
            Op::Equals => a == b,
            Op::NotEquals => a != b,
            Op::Like => {
                a.contains(b)
            }
            _ => panic!("Called compare_str on a non-string operator")
        }
    }
}


#[derive(Debug, PartialEq)]
pub enum Value {
    S(String),
    Unitless(i32),
    Bytes(i32),
    Percent(f32),
}

impl Value {
    fn build_string(s: &str) -> Self {
        Value::S(s.to_string())
    }

}



#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_value_bytes_regex() {
        use BYTES_REGEX;
        {
            let m = BYTES_REGEX.captures("1248").unwrap();
            let num_part = m.get(1).unwrap();
            assert_eq!(num_part.as_str(), "1248");
            assert!(m.get(2).is_none());
        }
        
        {
            let m = BYTES_REGEX.captures("4KiB").unwrap();
            let num_part = m.get(1).unwrap();
            let unit_part = m.get(2).unwrap();
            assert_eq!(num_part.as_str(), "4");
            assert_eq!(unit_part.as_str(), "KiB");
        }
        {
            let m = BYTES_REGEX.captures("16MB").unwrap();
            let num_part = m.get(1).unwrap();
            let unit_part = m.get(2).unwrap();
            assert_eq!(num_part.as_str(), "16");
            assert_eq!(unit_part.as_str(), "MB");
        }

    }

    #[test]
    fn test_build_value() {
        let value = Field::Rss.build_value_from_str("4KiB").unwrap();
        println!("{:?}", value);
        assert_eq!(value, Value::Bytes(4096));
        
        let value = Field::Rss.build_value_from_str("6MB").unwrap();
        println!("{:?}", value);
        assert_eq!(value, Value::Bytes(6000000));

        let value = Field::Rss.build_value_from_str("0x4q");
        assert!(value.is_err());

        let value = Field::Rss.build_value_from_str("4%").unwrap();
        assert_eq!(value, Value::Percent(0.04f32));




    }

}

#[cfg(test)]
extern crate libc;

extern crate chrono;

use {BYTES_REGEX, MEMINFO, DURATION_REGEX};
use procfs::{Process, ProcResult, MMapPath, ProcState};
use util;
use chrono::offset::Local;
use chrono::Duration;

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
    pub fn evaluate(&self, p: &Process) -> Result<bool, String> {
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
                (Field::Age, op, Value::Duration(dur)) => {
                    let proc_age = Local::now() - p.stat.starttime();
                    Ok(op.compare_numeric(proc_age, *dur))
                },
                (Field::Cmdline, op, Value::S(s)) => {
                    let full_cmd = p.cmdline().unwrap().join(" ");
                    Ok(op.compare_str(&full_cmd, s))
                }
                (Field::Maps, op, Value::S(s)) => 
                    // check to see if this string is in the pathname of any of the maps of this
                    // process
                    if let ProcResult::Ok(maps) = p.maps() {
                        Ok(maps.iter().any(|map| match map.pathname {
                            MMapPath::Path(ref p) => op.compare_str(&p.to_string_lossy(), s),
                            _ => false
                        }))
                    } else {
                        Ok(false)
                    },
                (Field::State, op, Value::State(state)) => Ok(op.compare_eq(p.stat.state(), *state)),
                (Field::Cwd, op, Value::S(s)) => {
                    match p.cwd() {
                        ProcResult::Ok(cwd) => Ok(op.compare_str(&cwd.to_string_lossy(), s)),
                        _ => Ok(false)
                    }
                }

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
    Age,
    Maps,
    State,
    Cwd,
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
            "age" => Ok(Field::Age),
            "maps" => Ok(Field::Maps),
            "state" => Ok(Field::State),
            "cwd" => Ok(Field::Cwd),
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
            Field::Age => {
                DURATION_REGEX.captures(s)
                    .and_then(|caps| {
                        Some((caps.get(1)?.as_str(), caps.get(2)?.as_str()))
                    })
                    .and_then(|(num_part, unit_part)| {
                        let num_part = i64::from_str_radix(num_part, 10).ok()?;
                        let now = Local::now();

                        match unit_part {
                            "s" | "sec" | "second" | "seconds" => Some(Value::Duration(Duration::seconds(num_part))),
                            "m" | "min" | "minute" | "minutes" => Some(Value::Duration(Duration::minutes(num_part))),
                            "h" | "hr" | "hour" | "hours" => Some(Value::Duration(Duration::hours(num_part))),
                            "d" | "day" | "days" => Some(Value::Duration(Duration::days(num_part))),
                            _ => None
                        }

                    })
                    .ok_or(format!("Unable to parse {:?} as a duration or date", s))
            }
            Field::Maps =>  Ok(Value::build_string(s)),
            Field::State => {
                if s.len() == 1 {
                    ProcState::from_char(s.chars().next().unwrap()).map(Value::State).ok_or(format!("Unable to parse {:?} as a process state", s))
                } else {
                    match s {
                        "running" => Ok(Value::State(ProcState::Running)),
                        "sleeping" => Ok(Value::State(ProcState::Sleeping)),
                        "waiting" => Ok(Value::State(ProcState::Waiting)),
                        "zombie" => Ok(Value::State(ProcState::Zombie)),
                        "stopped" => Ok(Value::State(ProcState::Stopped)),
                        "tracing" => Ok(Value::State(ProcState::Tracing)),
                        "dead" => Ok(Value::State(ProcState::Dead)),
                        "wakekill" => Ok(Value::State(ProcState::Wakekill)),
                        "waking" => Ok(Value::State(ProcState::Waking)),
                        "parked" => Ok(Value::State(ProcState::Parked)),
                        _ => Err(format!("Unable to parse {:?} as a process state", s))
                    }
                }

            }
            Field::Cwd =>  Ok(Value::build_string(s)),
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
    fn compare_eq<T>(&self, a: T, b: T) -> bool
    where T: PartialEq  {
        match *self {
            Op::Unknown(ref s) => panic!("Called compare_str on an unknown operator {}", s),
            Op::Equals => a == b,
            Op::NotEquals => a != b,
            _ => panic!("Called compare_eq on a non-equality operator"),
        }
    }
}


#[derive(Debug, PartialEq)]
pub enum Value {
    S(String),
    Unitless(i32),
    Bytes(i32),
    Percent(f32),
    Duration(chrono::Duration),
    Date(chrono::DateTime<Local>),
    State(ProcState)

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

        let value = Field::Age.build_value_from_str("5s").unwrap();
        assert_eq!(value, Value::Duration(chrono::Duration::seconds(5)));
        //if let Value::Duration(d) = value {
        //    assert_eq!(d
        //}


    }

}

#![feature(
    type_alias_enum_variants,
    bind_by_move_pattern_guards,
    slice_patterns
)]

mod program;
mod values;

use program::{Inst, Program, Type};
use std::cmp::{Ord, Ordering};
use std::collections::HashMap;
use values::{AbstractVal, Config, Instantiation};

pub const NUM_LOCALS: usize = 3;
pub const MAX_INSTS: usize = 10;

fn interpret_insts_with_config(
    program: &[Inst],
    mut config: Config,
) -> Instantiation {
    match program {
        [] => Instantiation::new(config),
        [Inst::Get(n), rest..] => {
            config.stack.push(config.locals[*n as usize].clone());
            interpret_insts_with_config(rest, config)
        }
        [Inst::Set(n), rest..] => {
            config.locals[*n as usize] = config.stack.pop().unwrap();
            interpret_insts_with_config(rest, config)
        }
        [Inst::Drop, rest..] => {
            config.stack.pop();
            interpret_insts_with_config(rest, config)
        }
        [Inst::Op(Type { from, to }), rest..] => {
            let params = {
                let mut params = Vec::new();
                for _ in 0..*from {
                    params.push(config.stack.pop().unwrap())
                }
                params
            };
            for i in 0..*to {
                config
                    .stack
                    .push(AbstractVal::Combined(i as u32, params.clone()));
            }
            interpret_insts_with_config(rest, config)
        }
        [Inst::If(left, right), rest..] => {
            let pivot = config.stack.pop().unwrap();
            let left_prog = {
                let mut prog = left.clone();
                prog.insts.extend_from_slice(rest);
                prog
            };
            let left_result =
                interpret_insts_with_config(&left_prog.insts, config.clone());
            let right_prog = {
                let mut prog = right.clone();
                prog.insts.extend_from_slice(rest);
                prog
            };
            let right_result =
                interpret_insts_with_config(&right_prog.insts, config);
            Instantiation::combined(pivot, left_result, right_result)
        }
    }
}

pub fn interpret(program: &Program) -> Instantiation {
    interpret_insts_with_config(&program.insts, Config::new())
}

#[derive(Default)]
struct SmallProgs {
    mvp: Option<Program>,
    multivalue: Option<Program>,
}

fn main() {
    let mut program = Program {
        insts: Vec::<Inst>::new(),
    };
    let mut count = 0;
    let mut results: HashMap<Instantiation, SmallProgs> = HashMap::new();
    loop {
        count += 1;
        // println!("{}", program);
        let instance = interpret(&program);
        let progs = results.entry(instance).or_default();
        let slot = if program.multivalue() {
            &mut progs.multivalue
        } else {
            &mut progs.mvp
        };
        match slot {
            Some(other) => {
                match Ord::cmp(&program.get_size(), &other.get_size()) {
                    Ordering::Less => *slot = Some(program.clone()),
                    Ordering::Equal => {
                        if &mut program < other {
                            *slot = Some(program.clone())
                        }
                    }
                    Ordering::Greater => {}
                }
            }
            None => *slot = Some(program.clone()),
        }
        if program.increment().is_none() {
            break;
        }
    }

    for (_, SmallProgs { mvp, multivalue }) in results {
        match (mvp, multivalue) {
            (Some(mvp), Some(multivalue)) => {
                if multivalue.get_size() < mvp.get_size() {
                    println!("MVP:   {}", mvp);
                    println!("Multi: {}\n", multivalue);
                }
            }
            _ => {}
        }
    }

    println!("{:}", count);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interpret_empty() {
        assert_eq!(
            interpret(&Program { insts: Vec::new() }),
            Instantiation::new(Config::new())
        )
    }

    #[test]
    fn nop_get_set() {
        // Get(1), If[{Get(2), Set(1), Get(0), Set(0)}, {}], Get(0)
        assert_eq!(
            interpret(&Program {
                insts: vec![
                    Inst::Get(1),
                    Inst::If(
                        Program {
                            insts: vec![
                                Inst::Get(2),
                                Inst::Set(1),
                                Inst::Get(0),
                                Inst::Set(0)
                            ]
                        },
                        Program { insts: Vec::new() }
                    ),
                    Inst::Get(0)
                ]
            }),
            interpret(&Program {
                insts: vec![
                    Inst::Get(1),
                    Inst::If(
                        Program {
                            insts: vec![Inst::Get(2), Inst::Set(1), Inst::Drop]
                        },
                        Program { insts: Vec::new() }
                    ),
                    Inst::Get(0)
                ]
            })
        );
    }
}

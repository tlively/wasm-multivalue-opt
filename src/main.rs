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

// returns true if the left branch of all Ifs is less than the right branch
fn has_normalized_ifs(program: &[Inst]) -> bool {
    match program {
        [] => true,
        [Inst::If(left, right), rest..] => {
            left < right
                && has_normalized_ifs(&left.insts)
                && has_normalized_ifs(&right.insts)
                && has_normalized_ifs(rest)
        }
        [_, rest..] => has_normalized_ifs(rest),
    }
}

// Some "smallest" programs still have dead stores because they
// introduce a local, allowing another local to be used earlier in the
// program where it would otherwise not be allowed, for example in
// Get(1), Get(2), If[{Get(2)}, {Get(1), Set(1), Get(0)}]. The
// equivalent version of this without a dead store would be
// Get(2), Get(1), If[{Get(1)}, {Get(0)}]
fn has_dead_store(program: &[Inst]) -> bool {
    match program {
        [] => false,
        [Inst::Get(a), Inst::Set(b), ..] if a == b => true,
        [Inst::If(left, right), rest..] => {
            has_dead_store(rest)
                || has_dead_store(&left.insts)
                || has_dead_store(&right.insts)
        }
        [_, rest..] => has_dead_store(rest),
    }
}

fn has_trivially_gluable_ifs(program: &[Inst]) -> bool {
    match program {
        [.., Inst::Get(a), Inst::If(_, _), Inst::Get(b), Inst::If(_, _)]
            if a == b =>
        {
            true
        }
        [.., Inst::Get(a), Inst::If(_, _), Inst::Get(_), Inst::Get(b), Inst::If(_, _)]
            if a == b =>
        {
            true
        }
        _ => false,
    }
}

// A very common optimization enabled by multivalue is to move a
// common instruction from both branches of an If to be prior to the
// If or after the If. Filter this out to help find other interesting
// patterns.
fn has_trivial_opt(program: &[Inst]) -> bool {
    match program {
        [] => false,
        [Inst::If(Program { insts: left }, Program { insts: right }), rest..] =>
        {
            let mut has_opt = false;
            if let ([l, ..], [r, ..]) = (left.as_slice(), right.as_slice()) {
                has_opt = l == r;
            }
            if let ([.., l], [.., r]) = (left.as_slice(), right.as_slice()) {
                has_opt = has_opt || l == r;
            }
            if has_opt {
                true
            } else {
                has_trivial_opt(rest)
                    || has_trivial_opt(&left)
                    || has_trivial_opt(&right)
            }
        }
        [_, rest..] => has_trivial_opt(rest),
    }
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
        if program.increment().is_none() {
            break;
        }

        // println!("{}", program);
        let instance = interpret(&program);
        let is_multi = program.multivalue();
        let progs = results.entry(instance).or_default();
        let slot = if is_multi {
            &mut progs.multivalue
        } else {
            &mut progs.mvp
        };
        let is_better = slot.as_ref().map_or(true, |other| {
            match Ord::cmp(&program.get_size(), &other.get_size()) {
                Ordering::Less => true,
                Ordering::Equal => &program < other,
                Ordering::Greater => false,
            }
        });
        if is_better {
            *slot = Some(program.clone());
        }
    }

    // (difference, mvp, multivalue)
    let mut sorted_results: Vec<(usize, Program, Program)> = results
        .drain()
        .filter_map(|(_, progs)| match progs {
            SmallProgs {
                mvp: Some(mvp),
                multivalue: Some(multivalue),
            } => {
                let mvp_size = mvp.get_size();
                let multi_size = multivalue.get_size();
                // apply useful filters to eliminate redundant results
                if mvp_size <= multi_size
                    || (&mvp.insts).last() == (&multivalue.insts).last()
                    || (&multivalue.insts).last() == Some(&Inst::Set(0))
                    || has_trivial_opt(&mvp.insts)
                    || !has_normalized_ifs(&mvp.insts)
                    || has_dead_store(&mvp.insts)
                    || has_trivially_gluable_ifs(&mvp.insts)
                {
                    None
                } else {
                    Some((mvp_size - multi_size, mvp, multivalue))
                }
            }
            _ => None,
        })
        .collect();

    // order by smallest MVP then largest difference
    sorted_results.sort_by(|a, b| {
        Ord::cmp(&a.1.get_size(), &b.1.get_size())
            .then_with(|| Ord::cmp(&a.0, &b.0).reverse())
            .then_with(|| Ord::cmp(&a.1, &b.1))
    });

    for (i, (_, mvp, multivalue)) in sorted_results.iter().enumerate() {
        println!("{}", i);
        println!("MVP:   {}", mvp);
        println!("Multi: {}\n", multivalue);
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
        let program = Program {
            insts: vec![
                Inst::Get(1),
                Inst::If(
                    Program {
                        insts: vec![
                            Inst::Get(2),
                            Inst::Set(1),
                            Inst::Get(0),
                            Inst::Set(0),
                        ],
                    },
                    Program { insts: Vec::new() },
                ),
                Inst::Get(0),
            ],
        };
        assert!(has_dead_store(&program.insts));
        assert_eq!(
            interpret(&program),
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

    #[test]
    fn dead_store_in_branch() {
        // Get(1), Get(0), If[{Get(2)}, {Get(1), Set(1), Get(0)}]
        let prog = Program {
            insts: vec![
                Inst::Get(1),
                Inst::Get(0),
                Inst::If(
                    Program {
                        insts: vec![Inst::Get(2)],
                    },
                    Program {
                        insts: vec![Inst::Get(1), Inst::Set(1), Inst::Get(0)],
                    },
                ),
            ],
        };
        assert!(has_dead_store(&prog.insts));
    }

    #[test]
    fn trivial_opt_head() {
        // Get(0), If[{Get(0), Set(1)}, {Get(0), Set(2), Get(1), Set(0)}]
        let program = Program {
            insts: vec![
                Inst::Get(0),
                Inst::If(
                    Program {
                        insts: vec![Inst::Get(0), Inst::Set(1)],
                    },
                    Program {
                        insts: vec![
                            Inst::Get(0),
                            Inst::Set(2),
                            Inst::Get(1),
                            Inst::Set(0),
                        ],
                    },
                ),
            ],
        };
        assert!(has_trivial_opt(&program.insts));
    }

    #[test]
    fn trivial_opt_tail() {
        let program = Program {
            insts: vec![
                Inst::Get(0),
                Inst::If(
                    Program {
                        insts: vec![Inst::Get(1), Inst::Set(2)],
                    },
                    Program {
                        insts: vec![Inst::Get(0), Inst::Set(2)],
                    },
                ),
                Inst::Get(0),
            ],
        };
        assert!(has_trivial_opt(&program.insts));
    }

}

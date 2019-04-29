#![feature(
    type_alias_enum_variants,
    bind_by_move_pattern_guards,
    slice_patterns
)]

use bit_vec::BitVec;
use std::iter;

pub const NUM_LOCALS: usize = 3;
pub const MAX_INSTS: usize = 6;

#[derive(Debug, PartialEq, Eq, PartialOrd, Clone)]
pub struct Type {
    from: usize,
    to: usize,
}

impl Type {
    fn subtype(&self, other: &Type) -> bool {
        self.from <= other.from && self.to >= other.to
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd)]
pub enum Inst {
    Get(u8),
    Set(u8),
    Drop,
    Op(Type),
    If(Vec<Inst>, Vec<Inst>),
}

impl Inst {
    fn get_type(&self) -> Type {
        match self {
            Self::Get(_) => Type { from: 0, to: 1 },
            Self::Set(_) => Type { from: 1, to: 0 },
            Self::Drop => Type { from: 1, to: 0 },
            Self::Op(t) => t.clone(),
            Self::If(e1, e2) => {
                let (t1, t2) = (get_type(e1), get_type(e2));
                Type {
                    from: 1 + usize::max(t1.from, t2.from),
                    to: usize::min(t1.to, t2.to),
                }
            }
        }
    }

    fn get_size(&self) -> usize {
        match self {
            Self::If(left, right) => 1 + get_size(left) + get_size(right),
            _ => 1,
        }
    }
}

pub fn get_type(program: &[Inst]) -> Type {
    let mut stack_size: i32 = 0;
    let mut min_size: i32 = 0;
    for inst in program {
        let t = inst.get_type();
        stack_size -= t.from as i32;
        min_size = min_size.min(stack_size);
        stack_size += t.to as i32;
    }
    Type {
        from: -min_size as usize,
        to: stack_size as usize,
    }
}

pub fn get_size(program: &[Inst]) -> usize {
    match program {
        [] => 0,
        [first, rest..] => first.get_size() + get_size(rest),
    }
}

// calculate the largest local index we are allowed to use, which
// is the lesser of the largest local index and one more than the
// largest used local index.
fn next_local(program: &[Inst]) -> u8 {
    match program {
        [] => 0,
        [Inst::Get(l), rest..] | [Inst::Set(l), rest..] => {
            next_local(rest).max(l + 1).min(NUM_LOCALS as u8 - 1)
        }
        [Inst::If(left, right), rest..] => u8::max(
            u8::max(next_local(left), next_local(right)),
            next_local(rest),
        ),
        [_, rest..] => next_local(rest),
    }
}

// Find the next available instruction that contains a local
// index not greater than `max_local`, is not larger than
// `max_size`, and consumes no more than `stack_size`
// elements. Skip trying instructions that would require more
// stack values than are available.
fn increment_inst(
    inst: &mut Inst,
    stack_type: Type,
    max_size: usize,
    max_local: u8,
) -> Option<()> {
    let mut curr: Inst = inst.clone();
    loop {
        curr = match curr {
            Inst::Get(n) => {
                if n < max_local {
                    Inst::Get(n + 1)
                } else if stack_type.from >= 1 {
                    Inst::Set(0)
                } else {
                    return None;
                }
            }
            Inst::Set(n) => {
                if stack_type.from >= 1 && n < max_local {
                    Inst::Set(n + 1)
                } else if stack_type.from >= 1 {
                    Inst::Drop
                } else {
                    return None;
                }
            }
            Inst::Drop => {
                if stack_type.from >= 2 && stack_type.to <= NUM_LOCALS {
                    Inst::Op(Type {
                        from: 2,
                        to: usize::max(stack_type.to, 1),
                    })
                } else if stack_type.from >= 1 {
                    Inst::If(Vec::new(), Vec::new())
                } else {
                    return None;
                }
            }
            Inst::Op(Type { from, to }) => {
                let max_from = usize::min(stack_type.from, NUM_LOCALS);
                if stack.from >= from && to < NUM_LOCALS {
                    Inst::Op(Type { from, to: to + 1 })
                } else if stack.from > from && from < max_from {
                    Inst::Op(Type {
                        from: from + 1,
                        to: usize::max(stack_type.to, 1),
                    })
                } else if stack_type.from >= 1 {
                    Inst::If(Vec::new(), Vec::new())
                } else {
                    return None;
                }
            }
            Inst::If(mut left, mut right) => {
                if stack_type.from < 1 {
                    return None;
                };
                if let Some(_) = increment(
                    &mut left,
                    stack_type.from - 1,
                    max_size - 1 - get_size(&right),
                ) {
                    Inst::If(left, right)
                } else if let Some(_) =
                    increment(&mut right, stack_type.from - 1, max_size - 1)
                {
                    left.clear();
                    Inst::If(left, right)
                } else {
                    return None;
                }
            }
        };
        // increment newly-created Ifs so that left < right and all
        // Ifs have consistent types.
        if let Inst::If(left, right) = &curr {
            if left >= right || get_type(&left) != get_type(&right) {
                continue;
            }
        }
        if curr.get_type().subtype(&stack_type) {
            *inst = curr;
            return Some(());
        }
    }
}

pub fn increment(
    program: &mut Vec<Inst>,
    mut stack_size: usize,
    max_size: usize,
) -> Option<()> {
    // Increment first element. If that wraps, recurse on next
    // element. If there is no next element, add a new element.
    let mut curr: &mut [Inst] = program;
    let mut size = 0;
    loop {
        match curr {
            [] => {
                if get_size(&program) < max_size {
                    program.push(Inst::Get(0));
                    return Some(());
                } else {
                    return None;
                }
            }
            [ref mut first, rest..] => {
                let inst_size = max_size - size - get_size(rest);
                let stack_type = Type {
                    from: stack_size,
                    to: get_type(rest).from,
                };
                match increment_inst(
                    first,
                    stack_type,
                    inst_size,
                    next_local(rest),
                ) {
                    Some(_) => {
                        return Some(());
                    }
                    None => {
                        *first = Inst::Get(0);
                        size += first.get_size();
                        let t = first.get_type();
                        stack_size -= t.from;
                        stack_size += t.to;
                        curr = rest;
                    }
                }
            }
        }
    }
}

pub fn multivalue(program: &[Inst]) -> bool {
    fn multivalue_with_stack(program: &[Inst], stack_size: usize) -> bool {
        match program {
            [] => false,
            [first, rest..] => {
                let t = first.get_type();
                if let Inst::If(left, right) = first {
                    if t.from > 1
                        || t.to >= 1
                        || multivalue_with_stack(&left, stack_size - 1)
                        || multivalue_with_stack(&right, stack_size - 1)
                    {
                        return true;
                    }
                }
                multivalue_with_stack(rest, stack_size - t.from + t.to)
            }
        }
    }
    multivalue_with_stack(program, 0)
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub enum AbstractVal {
    Val(u8),
    Combined(u8, Vec<AbstractVal>),
}

impl Default for AbstractVal {
    fn default() -> AbstractVal {
        AbstractVal::Val(0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Config {
    locals: [AbstractVal; NUM_LOCALS],
    stack: Vec<AbstractVal>,
}

impl Config {
    fn new() -> Self {
        let locals = {
            let mut locals: [AbstractVal; NUM_LOCALS] = Default::default();
            for i in 0..NUM_LOCALS {
                locals[i] = AbstractVal::Val(i as u8);
            }
            locals
        };
        Config {
            locals,
            stack: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instantiation {
    assignees: Vec<AbstractVal>,
    configs: Vec<Config>,
}

impl Instantiation {
    pub fn new(config: Config) -> Self {
        Instantiation {
            assignees: Vec::new(),
            configs: vec![config],
        }
    }

    pub fn combined(pivot: AbstractVal, left: Self, right: Self) -> Self {
        if left == right {
            return left;
        }
        let assignees = {
            let mut vals: Vec<AbstractVal> = iter::once(pivot.clone())
                .chain(left.assignees.iter().cloned())
                .chain(right.assignees.iter().cloned())
                .collect();
            vals.sort();
            vals.dedup();
            vals
        };
        let pivot_index = assignees.iter().position(|v| v == &pivot).unwrap();
        let (left_indices, right_indices) = {
            let assignee_indices = |instance: &Instantiation| {
                (0..assignees.len())
                    .into_iter()
                    .filter(|&i| {
                        instance
                            .assignees
                            .iter()
                            .position(|v| v == &assignees[i])
                            .is_some()
                    })
                    .collect::<Vec<usize>>()
            };
            (assignee_indices(&left), assignee_indices(&right))
        };
        let num_configs = 1usize << (assignees.len() as u32);
        let mut configs = Vec::new();
        configs.reserve(num_configs);
        for assignment_bits in 0..num_configs {
            let assignments = BitVec::from_fn(assignees.len(), |idx| {
                (assignment_bits >> idx) & 1 == 1
            });
            // create index of a config in an input Instantiation
            // by combining the current assigments for each value
            // in that input Instantiation
            let config_index = |assignee_indices: &Vec<usize>| {
                assignee_indices.iter().enumerate().fold(
                    0,
                    |acc, (bit_idx, &assignee_idx)| {
                        acc + (assignments[assignee_idx] as usize)
                            * (1usize << (bit_idx as u32))
                    },
                )
            };
            if assignments[pivot_index] {
                // pivot value is true, choose the left config
                configs.push(left.configs[config_index(&left_indices)].clone());
            } else {
                // otherwise choose right config
                configs
                    .push(right.configs[config_index(&right_indices)].clone())
            }
        }
        Instantiation::canonicalized(Instantiation { assignees, configs })
    }

    fn canonicalized(self) -> Self {
        let Instantiation {
            mut assignees,
            mut configs,
        } = self;
        assignees = assignees
            .drain(..)
            .enumerate()
            .rev()
            .filter_map(|(assignee_index, assignee)| {
                // partition configs based on assignment to assignee
                let (left, right): (
                    Vec<(usize, &Config)>,
                    Vec<(usize, &Config)>,
                ) = configs
                    .iter()
                    .enumerate()
                    .partition(|(i, _)| (i >> assignee_index) & 1 == 1);
                // strip out indices, leaving only configs
                let left: Vec<&Config> =
                    left.into_iter().map(|(_, c)| c).collect();
                let right: Vec<&Config> =
                    right.into_iter().map(|(_, c)| c).collect();
                if left == right {
                    // assignees[i] is redundant, so remove half of the configs
                    configs = configs
                        .drain(..)
                        .enumerate()
                        .filter_map(|(i, config)| {
                            if (i >> assignee_index) & 1 == 1 {
                                Some(config)
                            } else {
                                None
                            }
                        })
                        .collect();
                    // filter out the redundant assignee
                    None
                } else {
                    Some(assignee)
                }
            })
            .rev()
            .collect();
        Instantiation { assignees, configs }
    }
}

fn interpret_with_config(
    program: &[Inst],
    mut config: Config,
) -> Instantiation {
    match program {
        [] => Instantiation::new(config),
        [Inst::Get(n), rest..] => {
            config.stack.push(config.locals[*n as usize].clone());
            interpret_with_config(rest, config)
        }
        [Inst::Set(n), rest..] => {
            config.locals[*n as usize] = config.stack.pop().unwrap();
            interpret_with_config(rest, config)
        }
        [Inst::Drop, rest..] => {
            config.stack.pop();
            interpret_with_config(rest, config)
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
                    .push(AbstractVal::Combined(i as u8, params.clone()));
            }
            interpret_with_config(rest, config)
        }
        [Inst::If(left, right), rest..] => {
            // Auto-drop to unify left and right branch types
            let (left_dropped, right_dropped) = {
                let left_result = get_type(&left).to;
                let right_result = get_type(&right).to;
                (
                    left_result.saturating_sub(right_result),
                    right_result.saturating_sub(left_result),
                )
            };
            let pivot = config.stack.pop().unwrap();
            let left_prog = {
                let mut prog = left.clone();
                prog.extend(iter::repeat(Inst::Drop).take(left_dropped));
                prog.extend_from_slice(rest);
                prog
            };
            let left_result = interpret_with_config(&left_prog, config.clone());
            let right_prog = {
                let mut prog = right.clone();
                prog.extend(iter::repeat(Inst::Drop).take(right_dropped));
                prog.extend_from_slice(rest);
                prog
            };
            let right_result = interpret_with_config(&right_prog, config);
            Instantiation::combined(pivot, left_result, right_result)
        }
    }
}

pub fn interpret(program: &[Inst]) -> Instantiation {
    interpret_with_config(program, Config::new())
}

fn main() {
    let mut program = Vec::<Inst>::new();
    let mut count = 0;
    while increment(&mut program, 0, MAX_INSTS).is_some() {
        count += 1;
        println!("{:?}", program);
    }
    // for _ in 0..25 {
    //     count += 1;
    //     if multivalue(&program) {
    //         println!("MULTIVALUE")
    //     }
    //     println!("{:?}\n=>\n{:#?}\n", &program, interpret(&program));
    //     if let None = increment(&mut program, 0, MAX_INSTS) {
    //         break;
    //     }
    // }
    println!("{:}", count);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interpret_empty() {
        let empty_instance = Instantiation {
            assignees: Vec::new(),
            configs: vec![Config::new()],
        };
        assert_eq!(interpret(&Vec::new()), empty_instance)
    }

    #[test]
    fn nop_combine() {
        let instance = Instantiation {
            assignees: Vec::new(),
            configs: vec![Config {
                stack: vec![AbstractVal::Val(0)],
                ..Config::new()
            }],
        };
        assert_eq!(
            Instantiation::combined(
                AbstractVal::Val(1),
                instance.clone(),
                instance.clone(),
            ),
            instance
        );
        let prog = vec![
            Inst::Get(1),
            Inst::If(vec![Inst::Get(0)], vec![Inst::Get(0)]),
        ];
        assert_eq!(interpret(&prog), instance);
    }

    #[test]
    fn simple_combine() {
        let left = Instantiation {
            assignees: Vec::new(),
            configs: vec![Config {
                stack: vec![AbstractVal::Val(1)],
                ..Config::new()
            }],
        };
        let right = Instantiation {
            assignees: Vec::new(),
            configs: vec![Config {
                stack: vec![AbstractVal::Val(2)],
                ..Config::new()
            }],
        };
        let result = Instantiation {
            assignees: vec![AbstractVal::Val(0)],
            configs: vec![right.configs[0].clone(), left.configs[0].clone()],
        };
        assert_eq!(
            Instantiation::combined(AbstractVal::Val(0), left, right),
            result
        );
        let prog = vec![
            Inst::Get(0),
            Inst::If(vec![Inst::Get(1)], vec![Inst::Get(2)]),
        ];
        assert_eq!(interpret(&prog), result);
    }

    #[test]
    fn pivot_eliminated_combine() {
        let left = Instantiation {
            assignees: vec![AbstractVal::Val(0)],
            configs: vec![
                Config {
                    stack: vec![AbstractVal::Val(1)],
                    ..Config::new()
                },
                Config {
                    stack: vec![AbstractVal::Val(2)],
                    ..Config::new()
                },
            ],
        };
        let right = Instantiation {
            assignees: vec![AbstractVal::Val(0)],
            configs: vec![
                Config {
                    stack: vec![AbstractVal::Val(2)],
                    ..Config::new()
                },
                Config {
                    stack: vec![AbstractVal::Val(1)],
                    ..Config::new()
                },
            ],
        };
        let result = Instantiation {
            assignees: Vec::new(),
            configs: vec![Config {
                stack: vec![AbstractVal::Val(2)],
                ..Config::new()
            }],
        };
        assert_eq!(
            Instantiation::combined(AbstractVal::Val(0), left, right),
            result
        );
    }
}

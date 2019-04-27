#![feature(
    type_alias_enum_variants,
    bind_by_move_pattern_guards,
    slice_patterns
)]

const NUM_LOCALS: usize = 3;
const MAX_INSTS: usize = 10;

#[derive(Debug, PartialEq, Eq, Clone)]
struct Type {
    from: usize,
    to: usize,
}

impl Type {
    fn subtype(&self, other: &Type) -> bool {
        self.from <= other.from && self.to >= other.to
    }
}

#[derive(Debug, Clone)]
enum Inst {
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

fn get_type(program: &[Inst]) -> Type {
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

fn get_size(program: &[Inst]) -> usize {
    match program {
        [] => 0,
        [first, rest..] => first.get_size() + get_size(rest),
    }
}

fn increment_program(
    program: &mut Vec<Inst>,
    mut stack_size: usize,
    max_size: usize,
) -> Option<()> {
    // calculate the largest local index we are allowed to use, which
    // is the lesser of the largest local index and one more than the
    // largest used local index.
    fn next_local(program: &[Inst]) -> u8 {
        match program {
            [] => 0,
            [Inst::Get(l), rest..] | [Inst::Set(l), rest..] => {
                next_local(rest).max(l + 1).min(NUM_LOCALS as u8 - 1)
            }
            [_, rest..] => next_local(rest),
        }
    }

    // Find the next available instruction that contains a local index
    // not greater than `max_local`, is not larger than `max_size`,
    // and consumes no more than `stack_size` elements.
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
                    if stack_type.from >= 2 {
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
                    if from < stack_type.from && to >= stack_type.to {
                        Inst::Op(Type { from: from + 1, to })
                    } else if from >= stack_type.from && to < NUM_LOCALS {
                        Inst::Op(Type {
                            from: 2,
                            to: to + 1,
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
                    } else if let Some(_) = increment_program(
                        &mut left,
                        stack_type.from - 1,
                        max_size - 1 - get_size(&right),
                    ) {
                        Inst::If(left, right)
                    } else if let Some(_) = increment_program(
                        &mut right,
                        stack_type.from - 1,
                        max_size - 1 - get_size(&left),
                    ) {
                        left.clear();
                        Inst::If(left, right)
                    } else {
                        return None;
                    }
                }
            };
            if curr.get_type().subtype(&stack_type) {
                *inst = curr;
                return Some(());
            }
        }
    }

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

#[derive(Debug)]
enum AbstractVal {
    Val(u8),
    Combined(u8, Vec<AbstractVal>),
}

struct Config {
    locals: [AbstractVal; NUM_LOCALS as usize],
    stack: Vec<AbstractVal>,
}

struct Instantiation {
    assignees: Vec<AbstractVal>,
    configs: Vec<Config>,
}

fn main() {
    let mut program = Vec::<Inst>::new();
    let mut count = 0;
    while increment_program(&mut program, 0, MAX_INSTS).is_some() {
        count += 1;
        println!("{:?}", program);
    }
    println!("{:}", count);
}

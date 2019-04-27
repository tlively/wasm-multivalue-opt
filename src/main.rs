#![feature(
    type_alias_enum_variants,
    bind_by_move_pattern_guards,
    slice_patterns
)]

pub const NUM_LOCALS: usize = 3;
pub const MAX_INSTS: usize = 7;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type {
    from: usize,
    to: usize,
}

impl Type {
    fn subtype(&self, other: &Type) -> bool {
        self.from <= other.from && self.to >= other.to
    }
}

#[derive(Debug, Clone)]
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
                let (t1, t2) = (program::get_type(e1), program::get_type(e2));
                Type {
                    from: 1 + usize::max(t1.from, t2.from),
                    to: usize::min(t1.to, t2.to),
                }
            }
        }
    }

    fn get_size(&self) -> usize {
        match self {
            Self::If(left, right) => {
                1 + program::get_size(left) + program::get_size(right)
            }
            _ => 1,
        }
    }
}

mod program {
    pub use super::{Inst, Type, NUM_LOCALS};

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
                    if stack_type.from >= 2 {
                        Inst::Op(Type {
                            from: 2,
                            to: usize::max(stack_type.to, 1).min(NUM_LOCALS),
                        })
                    } else if stack_type.from >= 1 {
                        Inst::If(Vec::new(), Vec::new())
                    } else {
                        return None;
                    }
                }
                Inst::Op(Type { from, to }) => {
                    let max_from = usize::min(stack_type.from, NUM_LOCALS);
                    if from < max_from && to >= stack_type.to {
                        Inst::Op(Type { from: from + 1, to })
                    } else if from >= max_from && to < NUM_LOCALS {
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
                    } else if let Some(_) = increment(
                        &mut left,
                        stack_type.from - 1,
                        max_size - 1 - get_size(&right),
                    ) {
                        Inst::If(left, right)
                    } else if let Some(_) = increment(
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
}

mod interpret {
    pub use super::{Inst, Type, NUM_LOCALS};

    #[derive(Debug, Clone)]
    pub enum AbstractVal {
        Val(u8),
        Combined(u8, Vec<AbstractVal>),
    }

    impl Default for AbstractVal {
        fn default() -> AbstractVal {
            AbstractVal::Val(0)
        }
    }

    #[derive(Debug, Clone)]
    pub struct Config {
        locals: [AbstractVal; NUM_LOCALS],
        stack: Vec<AbstractVal>,
    }

    pub struct Instantiation {
        assignees: Vec<AbstractVal>,
        configs: Vec<Config>,
    }

    fn interpret_with_config(
        program: &[Inst],
        mut config: Config,
    ) -> Instantiation {
        match program {
            [] => {
                return Instantiation {
                    assignees: Vec::new(),
                    configs: vec![config],
                }
            }
            [Inst::Get(n), rest..] => {
                config.stack.push(config.locals[*n as usize].clone());
                interpret_with_config(rest, config)
            }
            // TODO: others
        }
    }

    pub fn interpret(program: &[Inst]) -> Instantiation {
        let locals = {
            let mut locals: [AbstractVal; NUM_LOCALS] = Default::default();
            for i in 0..NUM_LOCALS {
                locals[i] = AbstractVal::Val(i as u8);
            }
            locals
        };
        let config = Config {
            locals,
            stack: Vec::new(),
        };
        interpret_with_config(program, config)
    }

}

fn main() {
    let mut program = Vec::<Inst>::new();
    let mut count = 0;
    while program::increment(&mut program, 0, MAX_INSTS).is_some() {
        count += 1;
        if program::multivalue(&program) {
            println!("{:?}", program);
        }
    }
    println!("{:}", count);
}

use std::cmp::{Ord, Ordering, PartialOrd};
use std::fmt;
use std::iter::Iterator;

use super::{MAX_INSTS, NUM_LOCALS};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Type {
    pub from: usize,
    pub to: usize,
}

impl Type {
    fn subtype(&self, other: &Type) -> bool {
        self.from <= other.from && self.to >= other.to
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Inst {
    Get(u32),
    Set(u32),
    Drop,
    Op(Type),
    If(Program, Program),
}

impl Inst {
    fn get_type(&self) -> Type {
        match self {
            Self::Get(_) => Type { from: 0, to: 1 },
            Self::Set(_) => Type { from: 1, to: 0 },
            Self::Drop => Type { from: 1, to: 0 },
            Self::Op(t) => t.clone(),
            Self::If(e1, e2) => {
                let (t1, t2) = (e1.get_type(), e2.get_type());
                assert_eq!(t1, t2);
                Type {
                    from: 1 + t1.from,
                    to: t1.to,
                }
            }
        }
    }

    fn get_size(&self) -> usize {
        match self {
            Self::If(left, right) => 1 + left.get_size() + right.get_size(),
            _ => 1,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub insts: Vec<Inst>,
}

impl AsRef<[Inst]> for Program {
    fn as_ref(&self) -> &[Inst] {
        &self.insts
    }
}

impl Ord for Program {
    fn cmp(&self, other: &Self) -> Ordering {
        let len_cmp = Ord::cmp(&self.insts.len(), &other.insts.len());
        match len_cmp {
            Ordering::Less | Ordering::Greater => len_cmp,
            Ordering::Equal => self
                .insts
                .iter()
                .zip(other.insts.iter())
                .rev()
                .find_map(|(this_inst, other_inst)| {
                    let inst_cmp = Ord::cmp(this_inst, other_inst);
                    match inst_cmp {
                        Ordering::Less | Ordering::Greater => Some(inst_cmp),
                        Ordering::Equal => None,
                    }
                })
                .unwrap_or(Ordering::Equal),
        }
    }
}

impl PartialOrd for Program {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Program {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        for inst in &self.insts {
            if first {
                first = false;
            } else {
                write!(formatter, ", ")?
            }
            match inst {
                Inst::Get(_) | Inst::Set(_) | Inst::Drop => {
                    write!(formatter, "{:?}", inst)?
                }
                Inst::Op(Type { from, to }) => {
                    write!(formatter, "Op({},{})", from, to)?
                }
                Inst::If(left, right) => {
                    write!(formatter, "If[{{{}}}, {{{}}}]", left, right)?
                }
            }
        }
        Ok(())
    }
}

impl Program {
    fn new() -> Self {
        Program { insts: Vec::new() }
    }

    fn get_type_insts(program: &[Inst]) -> Type {
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
            to: i32::max(stack_size, 0) as usize,
        }
    }

    pub fn get_type(&self) -> Type {
        Program::get_type_insts(&self.insts)
    }

    fn get_size_insts(program: &[Inst]) -> usize {
        match program {
            [] => 0,
            [first, rest..] => first.get_size() + Program::get_size_insts(rest),
        }
    }

    pub fn get_size(&self) -> usize {
        Program::get_size_insts(&self.insts)
    }

    fn next_local_insts(program: &[Inst]) -> u32 {
        match program {
            [] => 0,
            [Inst::Get(l), rest..] | [Inst::Set(l), rest..] => {
                Program::next_local_insts(rest)
                    .max(l + 1)
                    .min(NUM_LOCALS as u32 - 1)
            }
            [Inst::If(left, right), rest..] => u32::max(
                u32::max(left.next_local(), right.next_local()),
                Program::next_local_insts(rest),
            ),
            [_, rest..] => Program::next_local_insts(rest),
        }
    }

    // calculate the largest local index we are allowed to use, which
    // is the lesser of the largest local index and one more than the
    // largest used local index.
    fn next_local(&self) -> u32 {
        Program::next_local_insts(&self.insts)
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
        max_local: u32,
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
                        Inst::If(Program::new(), Program::new())
                    } else {
                        return None;
                    }
                }
                Inst::Op(Type { from, to }) => {
                    let max_from = usize::min(stack_type.from, NUM_LOCALS);
                    if stack_type.from >= from && to < NUM_LOCALS {
                        Inst::Op(Type { from, to: to + 1 })
                    } else if stack_type.from > from && from < max_from {
                        Inst::Op(Type {
                            from: from + 1,
                            to: usize::max(stack_type.to, 1),
                        })
                    } else if stack_type.from >= 1 {
                        Inst::If(Program::new(), Program::new())
                    } else {
                        return None;
                    }
                }
                Inst::If(mut left, mut right) => {
                    if stack_type.from < 1 {
                        return None;
                    };
                    if let Some(_) = left.increment_with_params(
                        stack_type.from - 1,
                        max_size - 1 - right.get_size(),
                        u32::max(
                            max_local,
                            Program::next_local_insts(&right.insts),
                        ),
                    ) {
                        Inst::If(left, right)
                    } else if let Some(_) = right.increment_with_params(
                        stack_type.from - 1,
                        max_size - 1,
                        max_local,
                    ) {
                        left.insts.clear();
                        Inst::If(left, right)
                    } else {
                        return None;
                    }
                }
            };
            // Increment Ifs until they have consistent types
            if let Inst::If(left, right) = &curr {
                if left.get_type() != right.get_type() {
                    continue;
                }
            }
            curr.get_type();
            if curr.get_type().subtype(&stack_type) {
                *inst = curr;
                return Some(());
            }
        }
    }

    fn increment_with_params(
        &mut self,
        mut stack_size: usize,
        max_size: usize,
        max_local: u32,
    ) -> Option<()> {
        // Increment first element. If that wraps, recurse on next
        // element. If there is no next element, add a new element.
        let mut curr: &mut [Inst] = &mut self.insts;
        let mut size = 0;
        loop {
            match curr {
                [] => {
                    if self.get_size() < max_size {
                        self.insts.push(Inst::Get(0));
                        return Some(());
                    } else {
                        return None;
                    }
                }
                [ref mut first, rest..] => {
                    let inst_size =
                        max_size - size - Program::get_size_insts(rest);
                    let stack_type = Type {
                        from: stack_size,
                        to: Program::get_type_insts(rest).from,
                    };
                    match Program::increment_inst(
                        first,
                        stack_type,
                        inst_size,
                        u32::max(max_local, Program::next_local_insts(rest)),
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

    pub fn increment(&mut self) -> Option<()> {
        self.increment_with_params(0, MAX_INSTS, 0)
    }

    pub fn multivalue(&self) -> bool {
        fn multivalue_with_stack(program: &[Inst], stack_size: usize) -> bool {
            match program {
                [] => false,
                [first, rest..] => {
                    let t = first.get_type();
                    if let Inst::If(left, right) = first {
                        if t.from > 1
                            || t.to > 1
                            || multivalue_with_stack(
                                &left.insts,
                                stack_size - 1,
                            )
                            || multivalue_with_stack(
                                &right.insts,
                                stack_size - 1,
                            )
                        {
                            return true;
                        }
                    }
                    multivalue_with_stack(rest, stack_size - t.from + t.to)
                }
            }
        }
        multivalue_with_stack(&self.insts, 0)
    }
}

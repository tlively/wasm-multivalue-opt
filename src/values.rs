use bit_vec::BitVec;
use std::{fmt, iter};

use super::NUM_LOCALS;

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum AbstractVal {
    Val(u32),
    Combined(u32, Vec<AbstractVal>),
}

impl Default for AbstractVal {
    fn default() -> AbstractVal {
        AbstractVal::Val(0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Config {
    pub locals: [AbstractVal; NUM_LOCALS],
    pub stack: Vec<AbstractVal>,
}

impl Config {
    pub fn new() -> Self {
        let locals = {
            let mut locals: [AbstractVal; NUM_LOCALS] = Default::default();
            for i in 0..NUM_LOCALS {
                locals[i] = AbstractVal::Val(i as u32);
            }
            locals
        };
        Config {
            locals,
            stack: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Instantiation {
    assignees: Vec<AbstractVal>,
    configs: Vec<Config>,
}

impl fmt::Display for Instantiation {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "{:?}\n", self.assignees)?;
        for config in &self.configs {
            write!(formatter, "{:?}\n", config)?;
        }
        Ok(())
    }
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

#[cfg(test)]
mod tests {
    use super::*;

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
    }
}

use std::collections::HashMap;
use anyhow::Result;
use num_traits::Zero;
use zmips_opcodes::BF;
use zmips_opcodes::instruction::Instruction;
use zmips_opcodes::regs::RegA;
use crate::errors::InstructionError::{ExecuteReturnFailureValue, IOOutOfBoundary, StepOutOfLimits};
use crate::errors::vm_err;
use crate::state::VMOutput::{FinalAnswer, PrinterWrite};

#[derive(Debug, Clone)]
pub struct VMState<'a> {
    pub program: &'a [Instruction],
    pub ram: HashMap<BF, BF>,
    pub registers: Vec<BF>,
    pub jump_stack: Vec<(BF, BF)>,
    pub pc: usize,
    pub step_count: usize,
    pub public_input_pointer: usize,
    pub secret_input_pointer: usize,
    pub halting: bool,
}

impl<'a> Default for VMState<'a> {
    fn default() -> Self {
        Self {
            program: &[],
            ram: Default::default(),
            registers: vec![Default::default(); 32],
            jump_stack: vec![],
            pc: 0,
            step_count: 0,
            public_input_pointer: 0,
            secret_input_pointer: 0,
            halting: false,
        }
    }
}

pub enum VMOutput {
    FinalAnswer(BF),
    PrinterWrite(BF),
}

pub const VM_STEPS_MAX: usize = 100;

impl<'a> VMState<'a> {
    pub fn new(program: &'a [Instruction]) -> Self {
        Self {
            program,
            ..Default::default()
        }
    }
    pub fn instruction_fetch(&self) -> Result<Instruction> {
        self.program.get(self.pc).ok_or(anyhow::anyhow!("PC out of bounds")).cloned()
    }
    fn memory_get(&self, mem_addr: &BF) -> BF {
        self.ram
            .get(mem_addr)
            .copied()
            .unwrap_or_else(BF::zero)
    }
    fn memory_set(&mut self, mem_addr: BF, data: BF) {
        self.ram.insert(mem_addr, data);
    }
    pub fn step(&mut self, public_input: &[BF], secret_input: &[BF]) -> Result<Option<VMOutput>> {
        let mut output: Option<VMOutput> = None;
        if self.step_count > VM_STEPS_MAX {
            return vm_err(StepOutOfLimits);
        }
        self.step_count += 1;
        let instruction = self.instruction_fetch()?;
        println!("fetch instruction: {}", instruction);
        match instruction {
            Instruction::BEQ((r1, r2, addr)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                let r2: &BF = &self.registers[v2];
                self.pc = if r1.value() == r2.value() {
                    addr.value() as usize
                } else {
                    self.pc + 1
                };
            }
            Instruction::BNE((r1, r2, addr)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                let r2: &BF = &self.registers[v2];
                self.pc = if r1.value() != r2.value() {
                    addr.value() as usize
                } else {
                    self.pc + 1
                };
            }
            Instruction::BLT((r1, r2, addr)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                let r2: &BF = &self.registers[v2];
                self.pc = if r1.value() < r2.value() {
                    addr.value() as usize
                } else {
                    self.pc + 1
                };
            }
            Instruction::BLE((r1, r2, addr)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                let r2: &BF = &self.registers[v2];
                self.pc = if r1.value() <= r2.value() {
                    addr.value() as usize
                } else {
                    self.pc + 1
                };
            }
            Instruction::BGT((r1, r2, addr)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                let r2: &BF = &self.registers[v2];
                self.pc = if r1.value() > r2.value() {
                    addr.value() as usize
                } else {
                    self.pc + 1
                };
            }
            Instruction::SEQ((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v2] =
                            BF::new((r1.value() == imm as u64) as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v2] = BF::new(
                            (r1.value() == BF::from(a).value()) as u64,
                        );
                    }
                }
                self.pc += 1;
            }
            Instruction::SNE((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v2] =
                            BF::new((r1.value() != imm as u64) as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v2] = BF::new(
                            (r1.value() != BF::from(a).value()) as u64,
                        );
                    }
                }
                self.pc += 1;
            }
            Instruction::SLT((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v2] =
                            BF::new((r1.value() < imm as u64) as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v2] = BF::new(
                            (r1.value() < BF::from(a).value()) as u64,
                        );
                    }
                }
                self.pc += 1;
            }
            Instruction::SLE((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v2] =
                            BF::new((r1.value() <= imm as u64) as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v2] = BF::new(
                            (r1.value() <= BF::from(a).value()) as u64,
                        );
                    }
                }
                self.pc += 1;
            }
            Instruction::J(addr) => {
                self.pc = addr.value() as usize;
            }
            Instruction::JR(r) => {
                self.pc = BF::from(r).value() as usize;
            }
            Instruction::LW((r1, a, r2)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        let addr = BF::from((imm as u64 + r2.value()) as u64);
                        self.registers[v1] = self.memory_get(&addr);
                    }
                    RegA::RegName(a) => {
                        let addr = BF::from(
                            (BF::from(a).value() + r2.value()) as u64,
                        );
                        self.registers[v1] = self.memory_get(&addr);
                    }
                }
                self.pc += 1;
            }
            Instruction::SW((r1, a, r2)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r1: &BF = &self.registers[v1];
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        let addr = BF::new((imm as u64 + r2.value()) as u64);
                        self.memory_set(addr, *r1);
                    }
                    RegA::RegName(a) => {
                        let addr = BF::new(
                            (BF::from(a).value() + r2.value()) as u64,
                        );
                        self.memory_set(addr, *r1);
                    }
                }
                self.pc += 1;
            }
            Instruction::ADD((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = *r2 + BF::from(imm);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] = *r2 + BF::from(a);
                    }
                }
                self.pc += 1;
            }
            Instruction::SUB((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = *r2 - BF::from(imm);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] = *r2 - BF::from(a);
                    }
                }
                self.pc += 1;
            }
            Instruction::MULT((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = *r2 * BF::from(imm);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] = *r2 * BF::from(a);
                    }
                }
                self.pc += 1;
            }
            Instruction::DIV((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = *r2 / BF::from(imm);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] = *r2 / BF::from(a);
                    }
                }
                self.pc += 1;
            }
            Instruction::MOD((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        // FIXME: this is may not the correct way to do it...
                        self.registers[v1] = BF::from(r2.value() % (imm as u64));
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] =
                            BF::from(r2.value() % BF::from(a).value());
                    }
                }
                self.pc += 1;
            }
            Instruction::MOVE((r, a)) => {
                let v1: usize = r.into();
                match a {
                    RegA::Imm(imm) => self.registers[v1] = BF::from(imm),
                    RegA::RegName(r2) => {
                        let v2: usize = r2.into();
                        self.registers[v1] = self.registers[v2];
                    }
                }
                self.pc += 1;
            }
            Instruction::LA((r, a)) => {
                let v1: usize = r.into();
                self.registers[v1] = a;
                self.pc += 1;
            }
            Instruction::AND((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = BF::from(r2.value() & imm as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] =
                            BF::from(r2.value() & BF::from(a).value());
                    }
                }
                self.pc += 1;
            }
            Instruction::XOR((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = BF::from(r2.value() ^ imm as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] =
                            BF::from(r2.value() ^ BF::from(a).value());
                    }
                }
                self.pc += 1;
            }
            Instruction::OR((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = BF::from(r2.value() | imm as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] =
                            BF::from(r2.value() ^ BF::from(a).value());
                    }
                }
                self.pc += 1;
            }
            Instruction::NOT((r1, _r2, a)) => {
                let v1: usize = r1.into();
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] =
                            BF::from(!(imm as u64) & (usize::MAX) as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] = BF::from(
                            BF::from(a).value() & (usize::MAX) as u64,
                        );
                    }
                }
                self.pc += 1;
            }
            Instruction::SLL((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = BF::from(r2.value() << imm as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] =
                            BF::from(r2.value() << BF::from(a).value());
                    }
                }
                self.pc += 1;
            }
            Instruction::SRL((r1, r2, a)) => {
                let v1: usize = r1.into();
                let v2: usize = r2.into();
                let r2: &BF = &self.registers[v2];
                match a {
                    RegA::Imm(imm) => {
                        self.registers[v1] = BF::from(r2.value() >> imm as u64);
                    }
                    RegA::RegName(a) => {
                        self.registers[v1] =
                            BF::from(r2.value() >> BF::from(a).value());
                    }
                }
                self.pc += 1;
            }
            Instruction::PUBREAD(r) => {
                let v1: usize = r.into();
                if let Some(data) = public_input.get(self.public_input_pointer) {
                    self.registers[v1] = *data;
                } else {
                    return vm_err(IOOutOfBoundary);
                }
                self.public_input_pointer += 1;
                self.pc += 1;
            }
            Instruction::SECREAD(r) => {
                let v1: usize = r.into();
                if let Some(data) = secret_input.get(self.secret_input_pointer) {
                    self.registers[v1] = *data;
                } else {
                    return vm_err(IOOutOfBoundary);
                }
                self.secret_input_pointer += 1;
                self.pc += 1;
            }
            Instruction::PUBSEEK((r, offset)) => {
                let v1: usize = r.into();
                match offset {
                    RegA::Imm(imm) => {
                        self.public_input_pointer = imm as usize;
                    }
                    RegA::RegName(source) => {
                        let v: usize = source.into();
                        self.public_input_pointer = self.registers[v].value() as usize;
                    }
                }
                if let Some(data) = public_input.get(self.public_input_pointer) {
                    self.registers[v1] = *data;
                } else {
                    return vm_err(IOOutOfBoundary);
                }
            }
            Instruction::SECSEEK((r, offset)) => {
                let v1: usize = r.into();
                match offset {
                    RegA::Imm(imm) => {
                        self.secret_input_pointer = imm as usize;
                    }
                    RegA::RegName(source) => {
                        let v: usize = source.into();
                        self.secret_input_pointer = self.registers[v].value() as usize;
                    }
                }
                if let Some(data) = secret_input.get(self.public_input_pointer) {
                    self.registers[v1] = *data;
                } else {
                    return vm_err(IOOutOfBoundary);
                }
            }
            Instruction::PRINT(r) => {
                let v1: usize = r.into();
                let r = self.registers[v1];
                output = Some(PrinterWrite(r));
                self.pc += 1;
            }
            Instruction::EXIT(r) => {
                let v1: usize = r.into();
                self.pc += 1;
                let r = &self.registers[v1];
                self.halting = true;
                if r.is_zero() {
                    output = Some(FinalAnswer(*r));
                } else {
                    return vm_err(ExecuteReturnFailureValue(*r));
                }
            }
            Instruction::ANSWER(r) => {
                let v1: usize = r.into();
                let r = self.registers[v1];
                output = Some(FinalAnswer(r));
                self.pc += 1;
                self.halting = true;
            }
        }
        Ok(output)
    }
}
use std::collections::HashMap;
use std::ops::Neg;
use anyhow::Result;
use ndarray::Array1;
use num_traits::{One, Zero};
use twenty_first::shared_math::traits::Inverse;
use zmips_opcodes::BF;
use zmips_opcodes::instruction::Instruction;
use zmips_opcodes::regs::{Reg, RegA};
use crate::errors::InstructionError::{ExecuteReturnFailureValue, IOOutOfBoundary, StepOutOfLimits};
use crate::errors::vm_err;
use crate::state::VMOutput::{FinalAnswer, PrinterWrite};

#[derive(Debug, Clone)]
pub struct VMState<'a> {
    pub program: &'a [Instruction],
    pub ram: HashMap<BF, BF>,
    pub registers: Vec<BF>,
    pub jump_trace: Vec<(BF, BF)>,
    pub pc: BF,
    pub step_count: BF,
    pub public_input_pointer: BF,
    pub secret_input_pointer: BF,
    pub halting: bool,
}

impl<'a> Default for VMState<'a> {
    fn default() -> Self {
        Self {
            program: &[],
            ram: Default::default(),
            registers: vec![Default::default(); 64],
            jump_trace: vec![],
            pc: Default::default(),
            step_count: Default::default(),
            public_input_pointer: Default::default(),
            secret_input_pointer: Default::default(),
            halting: false,
        }
    }
}

pub enum VMOutput {
    FinalAnswer(BF),
    PrinterWrite(BF),
}

pub const VM_STEPS_MAX: u64 = 100000;

impl<'a> VMState<'a> {
    pub fn new(program: &'a [Instruction]) -> Self {
        Self {
            program,
            ..Default::default()
        }
    }
    pub fn dump(&self) -> Array1<BF> {
        let mut r = Array1::zeros(crate::table::processor::PROCESS_TABLE_SZ);
        // 1. pc
        // 2. step count
        // 3. public_input_pointer
        // 4. secret_input_pointer
        // 5-69. registers
        r[0] = self.pc;
        r[1] = self.step_count;
        r[2] = self.public_input_pointer;
        r[3] = self.secret_input_pointer;
        let mut i = 5 - 1;
        for v in self.registers.iter() {
            r[i] = *v;
            i += 1;
        }
        r
    }
    pub fn instruction_fetch(&self) -> Result<Instruction> {
        self.program.get(self.pc.value() as usize).ok_or(anyhow::anyhow!("PC out of bounds")).cloned()
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
    fn reg_read(&self, r: Reg) -> BF {
        let v: usize = r.into();
        self.registers[v]
    }
    fn reg_write(&mut self, r: Reg, data: BF) {
        let v: usize = r.into();
        self.registers[v] = data;
    }
    fn pc_jump_else_step(&mut self, cond: bool, addr: BF) {
        self.pc = if cond {
            self.jump_trace.push((self.pc, addr));
            addr
        } else {
            self.pc + BF::one()
        };
    }
    pub fn step(&mut self, public_input: &[BF], secret_input: &[BF]) -> Result<Option<VMOutput>> {
        let mut output: Option<VMOutput> = None;
        if self.step_count.value() > VM_STEPS_MAX {
            return vm_err(StepOutOfLimits);
        }
        self.step_count = self.step_count + BF::one();
        let instruction = self.instruction_fetch()?;
        // println!("fetch instruction: {}", instruction);
        match instruction {
            Instruction::BEQ((r1, r2, addr)) => {
                self.pc_jump_else_step(self.reg_read(r1).value() == self.reg_read(r2).value(), addr);
            }
            Instruction::BNE((r1, r2, addr)) => {
                self.pc_jump_else_step(self.reg_read(r1).value() != self.reg_read(r2).value(), addr);
            }
            Instruction::BLT((r1, r2, addr)) => {
                self.pc_jump_else_step(self.reg_read(r1).value() <= self.reg_read(r2).value(), addr);
            }
            Instruction::BLE((r1, r2, addr)) => {
                self.pc_jump_else_step(self.reg_read(r1).value() <= self.reg_read(r2).value(), addr);
            }
            Instruction::BGT((r1, r2, addr)) => {
                self.pc_jump_else_step(self.reg_read(r1).value() > self.reg_read(r2).value(), addr);
            }
            Instruction::SEQ((r1, r2, a)) => {
                let r1 = self.reg_read(r1);
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r2, BF::new((r1.value() == imm as u64) as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r2, BF::new(
                            (r1.value() == BF::from(a).value()) as u64,
                        ));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::SNE((r1, r2, a)) => {
                let r1 = self.reg_read(r1);
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r2, BF::new((r1.value() != imm as u64) as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r2, BF::new(
                            (r1.value() != BF::from(a).value()) as u64,
                        ));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::SLT((r1, r2, a)) => {
                let r1 = self.reg_read(r1);
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r2, BF::new((r1.value() < imm as u64) as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r2, BF::new(
                            (r1.value() < BF::from(a).value()) as u64,
                        ));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::SLE((r1, r2, a)) => {
                let r1 = self.reg_read(r1);
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r2, BF::new((r1.value() <= imm as u64) as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r2, BF::new(
                            (r1.value() <= BF::from(a).value()) as u64,
                        ));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::J(addr) => {
                self.jump_trace.push((BF::from(self.pc), addr));
                self.pc = addr;
            }
            Instruction::JR(r) => {
                let addr = self.reg_read(r);
                self.jump_trace.push((BF::from(self.pc), addr));
                self.pc = addr;
            }
            Instruction::LW((r1, a, r2)) => {
                match a {
                    RegA::Imm(imm) => {
                        let addr = BF::from(imm) + self.reg_read(r2);
                        self.reg_write(r1, self.memory_get(&addr));
                    }
                    RegA::RegName(a) => {
                        let addr = self.reg_read(r2) + self.reg_read(a);
                        self.reg_write(r1, self.memory_get(&addr));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::SW((r1, a, r2)) => {
                match a {
                    RegA::Imm(imm) => {
                        let addr = BF::from(imm) + self.reg_read(r2);
                        self.memory_set(addr, self.reg_read(r1));
                    }
                    RegA::RegName(a) => {
                        let addr = self.reg_read(r2) + self.reg_read(a);
                        self.memory_set(addr, self.reg_read(r1));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::ADD((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r1, self.reg_read(r2) + BF::from(imm));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, self.reg_read(r2) + self.reg_read(a));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::SUB((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r1, self.reg_read(r2) - BF::from(imm));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, self.reg_read(r2) - self.reg_read(a));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::MULT((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r1, self.reg_read(r2) * BF::from(imm));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, self.reg_read(r2) * self.reg_read(a));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::DIV((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r1, self.reg_read(r2) / BF::from(imm));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, self.reg_read(r2) / self.reg_read(a));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::MOD((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        // FIXME
                        // self.reg_write(r1, self.reg_read(r2) % BF::from(imm));
                        self.reg_write(r1, self.reg_read(r2) - ((self.reg_read(r2) / BF::from(imm)) * BF::from(imm)));
                    }
                    RegA::RegName(a) => {
                        // self.reg_write(r1, self.reg_read(r2) % self.reg_read(a));
                        self.reg_write(r1, self.reg_read(r2) - ((self.reg_read(r2) / self.reg_read(a)) * self.reg_read(a)));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::MOVE((r, a)) => {
                match a {
                    RegA::Imm(imm) => self.reg_write(r, BF::from(imm)),
                    RegA::RegName(r2) => self.reg_write(r, self.reg_read(r2)),
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::LA((r, addr)) => {
                self.reg_write(r, addr);
                self.pc = self.pc + BF::one();
            }
            Instruction::AND((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        // FIXME
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() & imm as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() & self.reg_read(a).value()));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::XOR((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        // FIXME
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() ^ imm as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() ^ self.reg_read(a).value()));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::OR((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        // FIXME
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() | imm as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() | self.reg_read(a).value()));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::NOT((r1, _r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        self.reg_write(r1, BF::from(!imm));
                    }
                    RegA::RegName(a) => {
                        // FIXME: right?
                        self.reg_write(r1, self.reg_read(a).inverse());
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::SLL((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        // FIXME
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() << imm as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() << self.reg_read(a).value()));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::SRL((r1, r2, a)) => {
                match a {
                    RegA::Imm(imm) => {
                        // FIXME
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() >> imm as u64));
                    }
                    RegA::RegName(a) => {
                        self.reg_write(r1, BF::from(self.reg_read(r2).value() >> self.reg_read(a).value()));
                    }
                }
                self.pc = self.pc + BF::one();
            }
            Instruction::PUBREAD(r) => {
                if let Some(data) = public_input.get(self.public_input_pointer.value() as usize) {
                    self.reg_write(r, *data);
                } else {
                    return vm_err(IOOutOfBoundary);
                }
                self.public_input_pointer = self.public_input_pointer + BF::one();
                self.pc = self.pc + BF::one();
            }
            Instruction::SECREAD(r) => {
                if let Some(data) = secret_input.get(self.secret_input_pointer.value() as usize) {
                    self.reg_write(r, *data);
                } else {
                    return vm_err(IOOutOfBoundary);
                }
                self.secret_input_pointer = self.secret_input_pointer + BF::one();
                self.pc = self.pc + BF::one();
            }
            Instruction::PUBSEEK((r, offset)) => {
                match offset {
                    RegA::Imm(imm) => {
                        self.public_input_pointer = BF::from(imm);
                    }
                    RegA::RegName(source) => {
                        self.public_input_pointer = self.reg_read(source);
                    }
                }
                if let Some(data) = public_input.get(self.public_input_pointer.value() as usize) {
                    self.reg_write(r, *data);
                } else {
                    return vm_err(IOOutOfBoundary);
                }
            }
            Instruction::SECSEEK((r, offset)) => {
                match offset {
                    RegA::Imm(imm) => {
                        self.secret_input_pointer = BF::from(imm);
                    }
                    RegA::RegName(source) => {
                        self.secret_input_pointer = self.reg_read(source);
                    }
                }
                if let Some(data) = secret_input.get(self.public_input_pointer.value() as usize) {
                    self.reg_write(r, *data);
                } else {
                    return vm_err(IOOutOfBoundary);
                }
            }
            Instruction::PRINT(r) => {
                output = Some(PrinterWrite(self.reg_read(r)));
                self.pc = self.pc + BF::one();
            }
            Instruction::EXIT(r) => {
                self.halting = true;
                if self.reg_read(r).is_zero() {
                    output = Some(FinalAnswer(self.reg_read(r)));
                } else {
                    return vm_err(ExecuteReturnFailureValue(self.reg_read(r)));
                }
            }
            Instruction::ANSWER(r) => {
                output = Some(FinalAnswer(self.reg_read(r)));
                self.pc = self.pc + BF::one();
                self.halting = true;
            }
        }
        Ok(output)
    }
}
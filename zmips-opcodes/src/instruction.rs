use std::collections::HashMap;
use std::fmt::Display;
use std::vec;

use anyhow::bail;
use anyhow::Result;
use strum::EnumCount;
use strum::IntoEnumIterator;
use strum_macros::Display as DisplayMacro;
use strum_macros::EnumCount as EnumCountMacro;
use strum_macros::EnumIter;
use twenty_first::shared_math::b_field_element::BFieldElement;
use twenty_first::shared_math::b_field_element::BFIELD_ZERO;

use crate::regs::{Reg, RegA};
use triton_program::AbstractInstruction;
use AnInstruction::*;

/// An `Instruction` has `call` addresses encoded as absolute integers.
pub type Instruction = AnInstruction<BFieldElement, Reg, RegA>;

impl AbstractInstruction for Instruction {
    fn clone_(&self) -> Box<dyn AbstractInstruction> {
        Box::new(*self) as Box<dyn AbstractInstruction>
    }
}

pub const ALL_INSTRUCTIONS: [Instruction; Instruction::COUNT] = all_instructions_without_args();
pub const ALL_INSTRUCTION_NAMES: [&str; Instruction::COUNT] = all_instruction_names();

/// A `LabelledInstruction` has `call` addresses encoded as label names.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LabelledInstruction {
    /// Instructions belong to the ISA:
    ///
    /// <https://triton-vm.org/spec/isa.html>
    Instruction(AnInstruction<String, String, String>),

    /// Labels look like "`<name>:`" and are translated into absolute addresses.
    Label(String),
}

impl Display for LabelledInstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LabelledInstruction::Instruction(instr) => write!(f, "{instr}"),
            LabelledInstruction::Label(label_name) => write!(f, "{label_name}:"),
        }
    }
}

#[derive(Debug, DisplayMacro, Clone, Copy, PartialEq, Eq, Hash, EnumCountMacro)]
pub enum DivinationHint {}

/// A Triton VM instruction. See the
/// [Instruction Set Architecture](https://triton-vm.org/spec/isa.html)
/// for more details.
///
/// The type parameter `Dest` describes the type of addresses (absolute or labels).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, EnumCountMacro, EnumIter)]
pub enum AnInstruction<L: PartialEq + Default, R: PartialEq + Default, A: PartialEq + Default> {
    // Control flow
    BEQ((R, R, L)),
    BNE((R, R, L)),
    BLT((R, R, L)),
    BLE((R, R, L)),
    BGT((R, R, L)),
    SEQ((R, R, A)),
    SNE((R, R, A)),
    SLT((R, R, A)),
    SLE((R, R, A)),
    J(L),
    JR(R),

    // Memory access
    LW((R, A, R)),
    SW((R, A, R)),

    // Base field arithmetic on stack
    ADD((R, R, A)),
    SUB((R, R, A)),
    MULT((R, R, A)),
    DIV((R, R, A)),
    MOD((R, R, A)),
    MOVE((R, A)),
    LA((R, L)),

    // Bitwise arithmetic on stack
    AND((R, R, A)),
    XOR((R, R, A)),
    OR((R, R, A)),
    NOT((R, R, A)),
    SLL((R, R, A)),
    SRL((R, R, A)),

    // Read/write
    PUBREAD(R),
    SECREAD(R),
    PUBSEEK((R, A)),
    SECSEEK((R, A)),
    PRINT(R),
    EXIT(R),
    ANSWER(R),
}

impl<Dest: PartialEq + Default, R: PartialEq + Default, I: PartialEq + Default>
    AnInstruction<Dest, R, I>
{
    // /// Drop the specific argument in favor of a default one.
    // pub fn strip(&self) -> Self {
    //     self.clone()
    // }

    /// Assign a unique positive integer to each `Instruction`.
    pub fn opcode(&self) -> u32 {
        match self {
            BEQ(_) => 0,
            BNE(_) => 1,
            BLT(_) => 2,
            BLE(_) => 3,
            SEQ(_) => 4,
            SNE(_) => 5,
            SLT(_) => 6,
            SLE(_) => 7,
            J(_) => 8,
            JR(_) => 9,
            LW(_) => 10,
            SW(_) => 11,
            ADD(_) => 12,
            SUB(_) => 13,
            MULT(_) => 14,
            DIV(_) => 15,
            MOD(_) => 16,
            MOVE(_) => 17,
            LA(_) => 18,
            AND(_) => 19,
            XOR(_) => 20,
            NOT(_) => 21,
            SLL(_) => 22,
            SRL(_) => 23,
            PUBREAD(_) => 24,
            SECREAD(_) => 25,
            PUBSEEK(_) => 26,
            SECSEEK(_) => 27,
            PRINT(_) => 28,
            EXIT(_) => 29,
            ANSWER(_) => 30,
            OR(_) => 31,
            BGT(_) => 32,
        }
    }

    const fn name(&self) -> &'static str {
        match self {
            BEQ(_) => "beq",
            BNE(_) => "bne",
            BLT(_) => "blt",
            BLE(_) => "ble",
            BGT(_) => "bgt",
            SEQ(_) => "seq",
            SNE(_) => "sne",
            SLT(_) => "slt",
            SLE(_) => "sle",
            J(_) => "j",
            JR(_) => "jr",
            LW(_) => "lw",
            SW(_) => "sw",
            ADD(_) => "add",
            SUB(_) => "sub",
            MULT(_) => "mult",
            DIV(_) => "div",
            MOD(_) => "mod",
            MOVE(_) => "move",
            LA(_) => "la",
            AND(_) => "and",
            XOR(_) => "xor",
            OR(_) => "or",
            NOT(_) => "not",
            SLL(_) => "sll",
            SRL(_) => "srl",
            PUBREAD(_) => "pubread",
            SECREAD(_) => "secread",
            PUBSEEK(_) => "pubseek",
            SECSEEK(_) => "secseek",
            PRINT(_) => "print",
            EXIT(_) => "exit",
            ANSWER(_) => "answer",
        }
    }

    pub fn opcode_b(&self) -> BFieldElement {
        self.opcode().into()
    }

    pub fn size(&self) -> usize {
        // match matches!(self, Push(_) | Dup(_) | Swap(_) | Call(_)) {
        //     true => 2,
        //     false => 1,
        // }
        1
    }

    // /// Get the i'th instruction bit
    // pub fn ib(&self, arg: Ord8) -> BFieldElement {
    //     let opcode = self.opcode();
    //     let bit_number: usize = arg.into();
    //
    //     ((opcode >> bit_number) & 1).into()
    // }
}

impl<Dest: PartialEq + Default> AnInstruction<Dest, String, String> {
    fn map_call_address<F, NewDest: PartialEq + Default>(
        &self,
        f: F,
    ) -> AnInstruction<NewDest, Reg, RegA>
    where
        F: Fn(&Dest) -> NewDest,
        Dest: Clone,
    {
        match self {
            BEQ((r1, r2, addr)) => BEQ((r1.into(), r2.into(), f(addr))),
            BNE((r1, r2, addr)) => BNE((r1.into(), r2.into(), f(addr))),
            BLT((r1, r2, addr)) => BLT((r1.into(), r2.into(), f(addr))),
            BLE((r1, r2, addr)) => BLE((r1.into(), r2.into(), f(addr))),
            BGT((r1, r2, addr)) => BGT((r1.into(), r2.into(), f(addr))),
            SEQ((r1, r2, a)) => SEQ((r1.into(), r2.into(), a.into())),
            SNE((r1, r2, a)) => SNE((r1.into(), r2.into(), a.into())),
            SLT((r1, r2, a)) => SLT((r1.into(), r2.into(), a.into())),
            SLE((r1, r2, a)) => SLE((r1.into(), r2.into(), a.into())),
            J(label) => J(f(label)),
            JR(r) => JR(r.into()),
            LW((r1, a, r2)) => LW((r1.into(), a.into(), r2.into())),
            SW((r1, a, r2)) => SW((r1.into(), a.into(), r2.into())),
            ADD((r1, r2, a)) => ADD((r1.into(), r2.into(), a.into())),
            SUB((r1, r2, a)) => SUB((r1.into(), r2.into(), a.into())),
            MULT((r1, r2, a)) => MULT((r1.into(), r2.into(), a.into())),
            DIV((r1, r2, a)) => DIV((r1.into(), r2.into(), a.into())),
            MOD((r1, r2, a)) => MOD((r1.into(), r2.into(), a.into())),
            MOVE((r, a)) => MOVE((r.into(), a.into())),
            LA((r, a)) => LA((r.into(), f(a))),
            AND((r1, r2, a)) => AND((r1.into(), r2.into(), a.into())),
            XOR((r1, r2, a)) => XOR((r1.into(), r2.into(), a.into())),
            OR((r1, r2, a)) => OR((r1.into(), r2.into(), a.into())),
            NOT((r1, r2, a)) => NOT((r1.into(), r2.into(), a.into())),
            SLL((r1, r2, a)) => SLL((r1.into(), r2.into(), a.into())),
            SRL((r1, r2, a)) => SRL((r1.into(), r2.into(), a.into())),
            PUBREAD(r) => PUBREAD(r.into()),
            SECREAD(r) => SECREAD(r.into()),
            PUBSEEK((r, a)) => PUBSEEK((r.into(), a.into())),
            SECSEEK((r, a)) => SECSEEK((r.into(), a.into())),
            PRINT(r) => PRINT(r.into()),
            EXIT(r) => EXIT(r.into()),
            ANSWER(r) => ANSWER(r.into()),
        }
    }
}

impl<
        Dest: Display + PartialEq + Default,
        R: Display + PartialEq + Default + Clone,
        I: Display + PartialEq + Default + Clone,
    > Display for AnInstruction<Dest, R, I>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())?;
        match self {
            BEQ((r1, r2, addr)) => write!(f, " {}, {}, {}", r1, r2, addr),
            BNE((r1, r2, addr)) => write!(f, " {}, {}, {}", r1, r2, addr),
            BLT((r1, r2, addr)) => write!(f, " {}, {}, {}", r1, r2, addr),
            BLE((r1, r2, addr)) => write!(f, " {}, {}, {}", r1, r2, addr),
            BGT((r1, r2, addr)) => write!(f, " {}, {}, {}", r1, r2, addr),
            J(addr) => write!(f, " {}", addr),
            JR(r) => write!(f, " {}", r),
            LW((r1, a, r2)) => write!(f, " {}, {}({})", r1, a, r2),
            SW((r1, a, r2)) => write!(f, " {}, {}({})", r1, a, r2),
            ADD((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            SUB((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            MULT((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            DIV((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            MOD((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            MOVE((r, a)) => write!(f, " {}, {}", r, a),
            LA((r, a)) => write!(f, " {}, {}", r, a),
            AND((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            XOR((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            OR((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            NOT((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            SLL((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            SRL((r1, r2, a)) => write!(f, " {}, {}, {}", r1, r2, a),
            PUBREAD(r) => write!(f, " {}", r),
            SECREAD(r) => write!(f, " {}", r),
            PUBSEEK((r, a)) => write!(f, " {}, {}", r, a),
            SECSEEK((r, a)) => write!(f, " {}, {}", r, a),
            PRINT(r) => write!(f, " {}", r),
            EXIT(r) => write!(f, " {}", r),
            ANSWER(r) => write!(f, " {}", r),
            _ => Ok(()),
        }
    }
}

impl Instruction {
    pub fn args(&self) -> Vec<BFieldElement> {
        match self {
            BEQ((r1, r2, addr)) => vec![BFieldElement::from(r1), BFieldElement::from(r2), *addr],
            BNE((r1, r2, addr)) => vec![BFieldElement::from(r1), BFieldElement::from(r2), *addr],
            BLT((r1, r2, addr)) => vec![BFieldElement::from(r1), BFieldElement::from(r2), *addr],
            BLE((r1, r2, addr)) => vec![BFieldElement::from(r1), BFieldElement::from(r2), *addr],
            BGT((r1, r2, addr)) => vec![BFieldElement::from(r1), BFieldElement::from(r2), *addr],
            J(addr) => vec![*addr],
            _ => vec![],
        }
    }
}

impl TryFrom<u32> for Instruction {
    type Error = anyhow::Error;

    fn try_from(opcode: u32) -> Result<Self> {
        if let Some(instruction) =
            Instruction::iter().find(|instruction| instruction.opcode() == opcode)
        {
            Ok(instruction)
        } else {
            bail!("No instruction with opcode {opcode} exists.")
        }
    }
}

impl TryFrom<u64> for Instruction {
    type Error = anyhow::Error;

    fn try_from(opcode: u64) -> Result<Self> {
        (opcode as u32).try_into()
    }
}

impl TryFrom<usize> for Instruction {
    type Error = anyhow::Error;

    fn try_from(opcode: usize) -> Result<Self> {
        (opcode as u32).try_into()
    }
}

/// Convert a program with labels to a program with absolute positions
pub fn convert_labels(program: &[LabelledInstruction]) -> Vec<Instruction> {
    let mut label_map = HashMap::<String, usize>::new();
    let mut instruction_pointer: usize = 0;

    // 1. Add all labels to a map
    for labelled_instruction in program.iter() {
        match labelled_instruction {
            LabelledInstruction::Label(label_name) => {
                label_map.insert(label_name.clone(), instruction_pointer);
            }

            LabelledInstruction::Instruction(instr) => {
                instruction_pointer += instr.size();
            }
        }
    }

    // 2. Convert every label to the lookup value of that map
    program
        .iter()
        .flat_map(|labelled_instruction| convert_labels_helper(labelled_instruction, &label_map))
        .collect()
}

fn convert_labels_helper(
    instruction: &LabelledInstruction,
    label_map: &HashMap<String, usize>,
) -> Vec<Instruction> {
    match instruction {
        LabelledInstruction::Label(_) => vec![],

        LabelledInstruction::Instruction(instr) => {
            let unlabelled_instruction: AnInstruction<BFieldElement, Reg, RegA> = instr
                .map_call_address(|label_name| {
                    let label_not_found = format!("Label not found: {label_name}");
                    let absolute_address = label_map.get(label_name).expect(&label_not_found);
                    BFieldElement::new(*absolute_address as u64)
                });

            vec![unlabelled_instruction]
        }
    }
}

const DEFAULT_BRANCH_INFO: (Reg, Reg, BFieldElement) = (Reg::Zero, Reg::Zero, BFIELD_ZERO);
const DEFAULT_LOAD_SAVE: (Reg, RegA, Reg) = (Reg::Zero, RegA::RegName(Reg::Zero), Reg::Zero);
const DEFAULT_INFO3: (Reg, Reg, RegA) = (Reg::Zero, Reg::Zero, RegA::Imm(0));
const DEFAULT_INFO2: (Reg, RegA) = (Reg::Zero, RegA::Imm(0));
const DEFAULT_REG_R: Reg = Reg::Zero;

const fn all_instructions_without_args(
) -> [AnInstruction<BFieldElement, Reg, RegA>; Instruction::COUNT] {
    [
        BEQ(DEFAULT_BRANCH_INFO),
        BNE(DEFAULT_BRANCH_INFO),
        BLT(DEFAULT_BRANCH_INFO),
        BLE(DEFAULT_BRANCH_INFO),
        BGT(DEFAULT_BRANCH_INFO),
        SEQ(DEFAULT_INFO3),
        SNE(DEFAULT_INFO3),
        SLT(DEFAULT_INFO3),
        SLE(DEFAULT_INFO3),
        J(BFIELD_ZERO),
        JR(DEFAULT_REG_R),
        LW(DEFAULT_LOAD_SAVE),
        SW(DEFAULT_LOAD_SAVE),
        ADD(DEFAULT_INFO3),
        SUB(DEFAULT_INFO3),
        MULT(DEFAULT_INFO3),
        DIV(DEFAULT_INFO3),
        MOD(DEFAULT_INFO3),
        MOVE(DEFAULT_INFO2),
        LA((Reg::Zero, BFIELD_ZERO)),
        AND(DEFAULT_INFO3),
        XOR(DEFAULT_INFO3),
        OR(DEFAULT_INFO3),
        NOT(DEFAULT_INFO3),
        SLL(DEFAULT_INFO3),
        SRL(DEFAULT_INFO3),
        PUBREAD(DEFAULT_REG_R),
        SECREAD(DEFAULT_REG_R),
        PUBSEEK(DEFAULT_INFO2),
        SECSEEK(DEFAULT_INFO2),
        PRINT(DEFAULT_REG_R),
        EXIT(DEFAULT_REG_R),
        ANSWER(DEFAULT_REG_R),
    ]
}

const fn all_instruction_names() -> [&'static str; Instruction::COUNT] {
    let mut names = [""; Instruction::COUNT];
    let mut i = 0;
    while i < Instruction::COUNT {
        names[i] = ALL_INSTRUCTIONS[i].name();
        i += 1;
    }
    names
}

pub mod sample_programs {
    pub const SPECK128: &str = "
        move $t4, 32
        secread $t2
        secread $t3
        __L1__:
            srl $t5, $t3, 8
            sll $t6, $t3, 56
            or $t6, $t5, $t6
            add $t3, $t6, $t2
            secread $t7

            xor $t3, $t3, $t7
            srl $t5, $t2, 61
            sll $t6, $t2, 3
            or $t6, $t5, $t6
            xor $t2, $t6, $t3

            add $t1, $t1, 1
        bgt $t4, $t1, __L1__
        print $t2
        print $t3
        answer $t3
    ";
}

#[cfg(test)]
mod instruction_tests {
    // use itertools::Itertools;
    // use num_traits::One;
    // use num_traits::Zero;
    // use strum::EnumCount;
    // use strum::IntoEnumIterator;
    // use twenty_first::shared_math::b_field_element::BFieldElement;

    use crate::instruction::ALL_INSTRUCTIONS;
    use crate::program::Program;

    // use super::AnInstruction;
    // use super::AnInstruction::*;

    // #[test]
    // fn opcode_test() {
    //     // test for duplicates
    //     let mut opcodes = vec![];
    //     for instruction in AnInstruction::<BFieldElement, String>::iter() {
    //         assert!(
    //             !opcodes.contains(&instruction.opcode()),
    //             "Have different instructions with same opcode."
    //         );
    //         opcodes.push(instruction.opcode());
    //     }
    //
    //     for opc in opcodes.iter() {
    //         println!(
    //             "opcode {} exists: {}",
    //             opc,
    //             AnInstruction::<BFieldElement, String>::try_from(*opc).unwrap()
    //         );
    //     }
    //
    //     // assert size of list corresponds to number of opcodes
    //     assert_eq!(
    //         AnInstruction::<BFieldElement, String>::COUNT,
    //         opcodes.len(),
    //         "Mismatch in number of instructions!"
    //     );
    //
    //     // test for width
    //     let max_opcode: u32 = AnInstruction::<BFieldElement, String>::iter()
    //         .map(|inst| inst.opcode())
    //         .max()
    //         .unwrap();
    //     let mut num_bits = 0;
    //     while (1 << num_bits) < max_opcode {
    //         num_bits += 1;
    //     }
    //     assert!(
    //         num_bits <= Ord8::COUNT,
    //         "Biggest instruction needs more than {} bits :(",
    //         Ord8::COUNT
    //     );
    //
    //     // assert consistency
    //     for instruction in AnInstruction::<BFieldElement, String>::iter() {
    //         assert!(
    //             instruction == instruction.opcode().try_into().unwrap(),
    //             "instruction to opcode map must be consistent"
    //         );
    //     }
    // }

    // #[test]
    // fn parse_push_pop_test() {
    //     let code = "
    //         push 1
    //         push 1
    //         add
    //         pop
    //     ";
    //     let program = Program::from_code(code).unwrap();
    //     let instructions = program.into_iter().collect_vec();
    //     let expected = vec![
    //         Push(BFieldElement::one()),
    //         Push(BFieldElement::one()),
    //         ADD,
    //         Pop,
    //     ];
    //
    //     assert_eq!(expected, instructions);
    // }

    #[test]
    fn fail_on_duplicate_labels_test() {
        let code = "
            push 2
            call foo
            bar: push 2
            foo: push 3
            foo: push 4
            halt
        ";
        let program = Program::from_code(code);
        assert!(
            program.is_err(),
            "Duplicate labels should result in a parse error"
        );
    }

    // #[test]
    // fn ib_registers_are_binary_test() {
    //     use Ord8::*;
    //
    //     for instruction in ALL_INSTRUCTIONS {
    //         let all_ibs: [Ord8; Ord8::COUNT] = [IB0, IB1, IB2, IB3, IB4, IB5, IB6, IB7];
    //         for ib in all_ibs {
    //             let ib_value = instruction.ib(ib);
    //             assert!(
    //                 ib_value.is_zero() || ib_value.is_one(),
    //                 "IB{ib} for instruction {instruction} is 0 or 1 ({ib_value})",
    //             );
    //         }
    //     }
    // }

    #[test]
    fn instruction_to_opcode_to_instruction_is_consistent_test() {
        for instr in ALL_INSTRUCTIONS {
            assert_eq!(instr, instr.opcode().try_into().unwrap());
        }
    }

    #[test]
    fn print_all_instructions_and_opcodes() {
        for instr in ALL_INSTRUCTIONS {
            println!("{:>3} {: <10}", instr.opcode(), format!("{}", instr.name()));
        }
    }
}

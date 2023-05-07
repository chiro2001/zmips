use zmips_opcodes::program::Program;
use anyhow::Result;
use zmips_opcodes::BF;
use crate::state::{VMOutput, VMState};
use crate::table::aet::AlgebraicExecutionTable;

pub fn execute(program: &[Program]) -> Result<(AlgebraicExecutionTable, Vec<BF>)> {
    let mut aet = AlgebraicExecutionTable::new();
    let mut public_input = Vec::new();
    let mut secrete_input = Vec::new();
    let mut output = None;
    let mut state = VMState::new(program);
    let mut stdout = vec![];
    while !state.halting {
        output = state.step(&mut public_input, &mut secrete_input)?;
        if let Some(VMOutput::PrinterWrite(bf)) = output {
            stdout.push(bf);
        }
    }
    Ok((aet, stdout))
}
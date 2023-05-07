use zmips_opcodes::program::Program;
use anyhow::Result;
use zmips_opcodes::BF;
use crate::state::{VMOutput, VMState};
use crate::table::aet::AlgebraicExecutionTable;

pub fn execute(program: &Program) -> Result<(AlgebraicExecutionTable, Vec<BF>)> {
    let mut aet = AlgebraicExecutionTable::new(&program);
    let mut public_input = Vec::new();
    let mut secrete_input = Vec::new();
    let mut output = None;
    let mut state = VMState::new(program.instructions.as_slice());
    let mut stdout = vec![];
    while !state.halting {
        output = state.step(&mut public_input, &mut secrete_input)?;
        if let Some(VMOutput::PrinterWrite(bf)) = output {
            stdout.push(bf);
        }
    }
    Ok((aet, stdout))
}

#[cfg(test)]
mod test {
    use zmips_opcodes::parser::{parse, to_labelled};
    use zmips_opcodes::program::Program;
    use crate::vm::execute;

    #[test]
    fn execute_simple_code() {
        let code = parse(crate::example_codes::SIMPLE_CODE).unwrap();
        let program = Program::new(&to_labelled(&code));
        if let Ok((aet, stdout)) = execute(&program) {}
    }
}
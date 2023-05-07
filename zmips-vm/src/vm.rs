use zmips_opcodes::program::Program;
use anyhow::Result;
use zmips_opcodes::BF;
use crate::state::{VMOutput, VMState};
use crate::table::aet::AlgebraicExecutionTable;

pub fn execute<'a>(program: &'a Program, public_input: &'a [BF], secret_input: &'a [BF]) -> Result<(AlgebraicExecutionTable<'a>, Vec<BF>)> {
    let mut aet = AlgebraicExecutionTable::new(&program);
    let mut output;
    let mut state = VMState::new(program.instructions.as_slice());
    let mut stdout = vec![];
    while !state.halting {
        output = state.step(public_input, secret_input)?;
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
        if let Ok((aet, stdout)) = execute(&program, &[], &[]) {}
    }
}
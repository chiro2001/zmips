use zmips_opcodes::program::Program;
use anyhow::Result;
use zmips_opcodes::BF;
use crate::state::{VMOutput, VMState};
use crate::table::aet::AlgebraicExecutionTable;

pub fn tape_data_conv(input: &[u32]) -> Vec<BF> {
    input.iter().map(|x| BF::from(*x)).collect()
}

pub fn tape_data_conv64(input: &[u64]) -> Vec<BF> {
    let mut v = vec![];
    // input.iter().map(|x| BF::from(*x)).collect()
    for i in input {
        v.push(BF::from((i & 0xffffffff) as u32));
        v.push(BF::from(((i >> 32) & 0xffffffff) as u32));
    }
    v
}

pub fn execute<'a>(program: &'a Program, public_input: &'a [u64], secret_input: &[u64]) -> Result<(AlgebraicExecutionTable, Vec<BF>)> {
    let mut aet = AlgebraicExecutionTable::new(&program);
    let mut output;
    let mut state = VMState::new(program.instructions.as_slice());
    let mut stdout = vec![];
    let public_input = tape_data_conv64(public_input);
    let secret_input = tape_data_conv64(secret_input);
    while !state.halting {
        output = state.step(public_input.as_slice(), secret_input.as_slice())?;
        if let Some(output) = output {
            match output {
                VMOutput::FinalAnswer(ans) => aet.ans = Some(ans),
                VMOutput::PrinterWrite(bf) => stdout.push(bf),
            }
        }
        let processor_trace = state.dump();
        aet.processor_trace.push_row(processor_trace.view())?;
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
        if let Ok((aet, stdout)) = execute(&program, &[], &[]) {
            println!("{:?}", aet);
            if !stdout.is_empty() {
                println!("stdout:");
                for v in stdout {
                    println!("{}", v);
                }
            }
        }
    }

    #[test]
    fn execute_infinity_code() {
        let code = parse(crate::example_codes::INFINITY_CODE).unwrap();
        let program = Program::new(&to_labelled(&code));
        if let Err(e) = execute(&program, &[], &[]) {
            println!("pass test, expected err is {}", e);
        }
    }

    #[test]
    fn execute_speck128_code() {
        let code = parse(crate::example_codes::SPECK128).unwrap();
        let program = Program::new(&to_labelled(&code));
        let (aet, stdout) = execute(&program, &[], crate::example_codes::SPEC128_AUX_TAPE).unwrap();
        println!("{:?}", aet);
        if !stdout.is_empty() {
            println!("stdout:");
            for v in stdout {
                println!("{}", v);
            }
        }
    }

    #[test]
    fn execute_speck128_exp_code() {
        let code = parse(crate::example_codes::SPECK128_EXP).unwrap();
        let program = Program::new(&to_labelled(&code));
        let (aet, stdout) = execute(&program, &[], crate::example_codes::SPEC128_EXP_AUX_TAPE).unwrap();
        println!("{:?}", aet);
        if !stdout.is_empty() {
            println!("stdout:");
            for v in stdout {
                println!("{}", v);
            }
        }
    }
}
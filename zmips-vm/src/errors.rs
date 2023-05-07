use std::error::Error;
use std::fmt::{Display, Formatter};
use zmips_opcodes::BF;
use anyhow::Result;

#[derive(Debug, Clone)]
pub enum InstructionError {
    ExecuteReturnFailureValue(BF)
}

impl Display for InstructionError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            InstructionError::ExecuteReturnFailureValue(v) => write!(f, "program return value is not 0: {}", v),
        }
    }
}

impl Error for InstructionError {}

pub fn vm_err<T>(runtime_error: InstructionError) -> Result<T> {
    Err(vm_fail(runtime_error))
}

pub fn vm_fail(runtime_error: InstructionError) -> anyhow::Error {
    anyhow::Error::new(runtime_error)
}

use zmips_opcodes::BF;
use zmips_opcodes::program::Program;
use ndarray::Array2;

#[derive(Debug, Clone)]
pub struct AlgebraicExecutionTable {
    pub program: Program,
    pub processor_trace: Array2<BF>,
}

impl Default for AlgebraicExecutionTable {
    fn default() -> Self {
        Self { program: Default::default(), processor_trace: Array2::default([0, crate::table::processor::PROCESS_TABLE_SZ]) }
    }
}

impl AlgebraicExecutionTable {
    pub fn new(program: &Program) -> Self {
        Self { program: program.clone(), ..Default::default() }
    }
}
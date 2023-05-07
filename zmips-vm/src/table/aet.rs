use zmips_opcodes::BF;
use zmips_opcodes::program::Program;
use ndarray::Array2;

#[derive(Debug, Clone, Default)]
pub struct AlgebraicExecutionTable {
    pub program: Program,
    pub processor_trace: Array2<BF>,
}

impl AlgebraicExecutionTable {
    pub fn new(program: &Program) -> Self {
        Self { program: program.clone(), ..Default::default() }
    }
}
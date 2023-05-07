use zmips_opcodes::program::Program;

pub struct AlgebraicExecutionTable<'a> {
    pub program: &'a Program,
}

impl<'a> AlgebraicExecutionTable<'a> {
    pub fn new(program: &'a Program) -> Self {
        Self { program }
    }
}
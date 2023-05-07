pub mod table;
pub mod state;
pub mod vm;
pub mod errors;

mod example_codes {
    pub const SIMPLE_CODE: &'static str = "
    move $t1, 3
    answer $t1";
}
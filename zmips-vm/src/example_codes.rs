pub const SIMPLE_CODE: &'static str = "
move $t1, 3
print $t1
answer $t1";

pub const INFINITY_CODE: &'static str = "
move $t1, 2
loop:
add $t1, $t1, 1
print $t1
j loop";


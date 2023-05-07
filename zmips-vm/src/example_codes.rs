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

pub const SPECK128: &'static str = "
move $t4, 32
secread $t2
secread $t3
__L1__:
    srl $t5, $t3, 8
    sll $t6, $t3, 56
    or $t6, $t5, $t6
    add $t3, $t6, $t2
    secread $t7

    xor $t3, $t3, $t7
    srl $t5, $t2, 61
    sll $t6, $t2, 3
    or $t6, $t5, $t6
    xor $t2, $t6, $t3

    add $t1, $t1, 1
bgt $t4, $t1, __L1__
print $t2
print $t3
answer $t3
";

pub const SPEC128_AUX_TAPE: &'static [u64] = &[
    8388271400802151712,
    7809653424151160096,
    506097522914230528,
    3973647328251544329,
    17950655201463765084,
    14317489089963390601,
    94520569244079856,
    13113041638675238870,
    11776184413102243070,
    17659011194153809395,
    6013620206426604893,
    10220345547992904357,
    12845347822737599512,
    8448324625705747870,
    8707226797264135739,
    9733733602373445842,
    12177605352264808178,
    5220725559095716473,
    8583509032072235795,
    16764294123368103200,
    16628110658475527315,
    5580441256713131253,
    15879888747126354140,
    12690311127066449729,
    15535297226658592074,
    11685805855277634329,
    16152677378382430280,
    7446018314323557823,
    7284357927190751580,
    2652372895522723097,
    4081227539235714858,
    16057933008819905284,
    14212543182292431461,
    2421186661733812543
];

pub const SPECK128_EXP: &'static str = "
move $t4, 31
# read key
secread $t3
secread $t0
# read pt
secread $t10
secread $t11
__L1__:
# encrypt
    srl $t5, $t11, 8
    sll $t6, $t11, 56
    or $t6, $t5, $t6
    add $t11, $t6, $t10
    xor $t11, $t11, $t3
    srl $t5, $t10, 61
    sll $t6, $t10, 3
    or $t6, $t5, $t6
    xor $t10, $t6, $t11
# expand
    srl $t5, $t0, 8
    sll $t6, $t0, 56
    or $t0, $t5, $t6
    add $t0, $t0, $t3
    xor $t0, $t0, $t9
    srl $t6, $t3, 61
    sll $t5, $t3, 3
    or $t3, $t5, $t6
    xor $t3, $t3, $t0


    add $t9, $t9, 1
bgt $t4, $t9, __L1__

srl $t5, $t11, 8
sll $t6, $t11, 56
or $t6, $t5, $t6
add $t11, $t6, $t10
xor $t11, $t11, $t3
srl $t5, $t10, 61
sll $t6, $t10, 3
or $t6, $t5, $t6
xor $t10, $t6, $t11

print $t10
print $t11
answer $t11
";

pub const SPEC128_EXP_AUX_TAPE: &'static [u64] = &[
    506097522914230528,
    1084818905618843912,
    8388271400802151712,
    7809653424151160096,
];


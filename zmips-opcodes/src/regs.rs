use std::fmt::{Display, Formatter};
use twenty_first::shared_math::b_field_element::BFieldElement;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Reg {
    #[default]
    Zero,
    At,
    V0,
    V1,
    A0,
    A1,
    A2,
    A3,
    T0,
    T1,
    T2,
    T3,
    T4,
    T5,
    T6,
    T7,
    S0,
    S1,
    S2,
    S3,
    S4,
    S5,
    S6,
    S7,
    T8,
    T9,
    K0,
    K1,
    Gp,
    Sp,
    Fp,
    Ra,
}
pub const REGS: [Reg; 32] = [
    Reg::Zero,
    Reg::At,
    Reg::V0,
    Reg::V1,
    Reg::A0,
    Reg::A1,
    Reg::A2,
    Reg::A3,
    Reg::T0,
    Reg::T1,
    Reg::T2,
    Reg::T3,
    Reg::T4,
    Reg::T5,
    Reg::T6,
    Reg::T7,
    Reg::S0,
    Reg::S1,
    Reg::S2,
    Reg::S3,
    Reg::S4,
    Reg::S5,
    Reg::S6,
    Reg::S7,
    Reg::T8,
    Reg::T9,
    Reg::K0,
    Reg::K1,
    Reg::Gp,
    Reg::Sp,
    Reg::Fp,
    Reg::Ra,
];

impl From<&str> for Reg {
    fn from(value: &str) -> Self {
        if value.len() < 2 {
            panic!("Invalid register name: {}", value);
        }
        // remove '$' prefix
        let value = match value.strip_prefix('$') {
            None => value,
            Some(v) => v,
        };
        match value {
            "zero" => Reg::Zero,
            "at" => Reg::At,
            "v0" => Reg::V0,
            "v1" => Reg::V1,
            "a0" => Reg::A0,
            "a1" => Reg::A1,
            "a2" => Reg::A2,
            "a3" => Reg::A3,
            "t0" => Reg::T0,
            "t1" => Reg::T1,
            "t2" => Reg::T2,
            "t3" => Reg::T3,
            "t4" => Reg::T4,
            "t5" => Reg::T5,
            "t6" => Reg::T6,
            "t7" => Reg::T7,
            "s0" => Reg::S0,
            "s1" => Reg::S1,
            "s2" => Reg::S2,
            "s3" => Reg::S3,
            "s4" => Reg::S4,
            "s5" => Reg::S5,
            "s6" => Reg::S6,
            "s7" => Reg::S7,
            "t8" => Reg::T8,
            "t9" => Reg::T9,
            "k0" => Reg::K0,
            "k1" => Reg::K1,
            "gp" => Reg::Gp,
            "sp" => Reg::Sp,
            "fp" => Reg::Fp,
            "ra" => Reg::Ra,
            _ => match value.parse::<usize>() {
                Ok(n) if n < 32 => REGS[n],
                _ => panic!("Unknown register: {}", value),
            },
        }
    }
}
impl From<&String> for Reg {
    fn from(value: &String) -> Self {
        value.as_str().into()
    }
}
impl From<&Reg> for String {
    fn from(value: &Reg) -> Self {
        format!("{:?}", value)
    }
}
impl Display for Reg {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let s: String = self.into();
        write!(f, "{}", s)
    }
}
impl From<Reg> for u32 {
    fn from(value: Reg) -> Self {
        (&value).into()
    }
}
impl From<Reg> for usize {
    fn from(value: Reg) -> Self {
        let v: u32 = (&value).into();
        v as usize
    }
}
impl From<&Reg> for u32 {
    fn from(value: &Reg) -> Self {
        match value {
            Reg::Zero => 0,
            Reg::At => 1,
            Reg::V0 => 2,
            Reg::V1 => 3,
            Reg::A0 => 4,
            Reg::A1 => 5,
            Reg::A2 => 6,
            Reg::A3 => 7,
            Reg::T0 => 8,
            Reg::T1 => 9,
            Reg::T2 => 10,
            Reg::T3 => 11,
            Reg::T4 => 12,
            Reg::T5 => 13,
            Reg::T6 => 14,
            Reg::T7 => 15,
            Reg::S0 => 16,
            Reg::S1 => 17,
            Reg::S2 => 18,
            Reg::S3 => 19,
            Reg::S4 => 20,
            Reg::S5 => 21,
            Reg::S6 => 22,
            Reg::S7 => 23,
            Reg::T8 => 24,
            Reg::T9 => 25,
            Reg::K0 => 26,
            Reg::K1 => 27,
            Reg::Gp => 28,
            Reg::Sp => 29,
            Reg::Fp => 30,
            Reg::Ra => 31,
        }
    }
}
impl From<Reg> for BFieldElement {
    fn from(value: Reg) -> Self {
        let n: u32 = value.into();
        n.into()
    }
}
impl From<&Reg> for BFieldElement {
    fn from(value: &Reg) -> Self {
        let n: u32 = value.into();
        n.into()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RegA {
    Imm(u32),
    RegName(Reg),
}

impl Default for RegA {
    fn default() -> Self {
        RegA::Imm(0)
    }
}
impl From<&String> for RegA {
    fn from(value: &String) -> Self {
        if let Some(value) = value.strip_prefix("0x") {
            let value = u32::from_str_radix(value, 16).unwrap();
            return RegA::Imm(value);
        }
        if let Some(value) = value.strip_prefix("0b") {
            let value = u32::from_str_radix(value, 2).unwrap();
            return RegA::Imm(value);
        }
        if let Some(value) = value.strip_prefix("0o") {
            let value = u32::from_str_radix(value, 8).unwrap();
            return RegA::Imm(value);
        }
        match value.parse::<u32>() {
            Ok(imm) => RegA::Imm(imm),
            Err(_) => RegA::RegName(value.into()),
        }
    }
}
impl From<&RegA> for BFieldElement {
    fn from(value: &RegA) -> Self {
        match value {
            RegA::Imm(imm) => (*imm).into(),
            RegA::RegName(r) => r.into(),
        }
    }
}
impl Display for RegA {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            RegA::Imm(imm) => write!(f, "{}", imm),
            RegA::RegName(r) => write!(f, "{}", r),
        }
    }
}

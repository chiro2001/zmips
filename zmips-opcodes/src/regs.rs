use std::fmt::{Display, Formatter};
use crate::BF;

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
    // extra regs: 16 extra temporal regs and 16 extra saved regs
    S8,
    S9,
    S10,
    S11,
    S12,
    S13,
    S14,
    S15,
    S16,
    S17,
    S18,
    S19,
    S20,
    S21,
    S22,
    S23,
    T10,
    T11,
    T12,
    T13,
    T14,
    T15,
    T16,
    T17,
    T18,
    T19,
    T20,
    T21,
    T22,
    T23,
    T24,
    T25,
}

pub const REGS: [Reg; 64] = [
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
    Reg::S8,
    Reg::S9,
    Reg::S10,
    Reg::S11,
    Reg::S12,
    Reg::S13,
    Reg::S14,
    Reg::S15,
    Reg::S16,
    Reg::S17,
    Reg::S18,
    Reg::S19,
    Reg::S20,
    Reg::S21,
    Reg::S22,
    Reg::S23,
    Reg::T10,
    Reg::T11,
    Reg::T12,
    Reg::T13,
    Reg::T14,
    Reg::T15,
    Reg::T16,
    Reg::T17,
    Reg::T18,
    Reg::T19,
    Reg::T20,
    Reg::T21,
    Reg::T22,
    Reg::T23,
    Reg::T24,
    Reg::T25,
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
            "s8" => Reg::S8,
            "s9" => Reg::S9,
            "s10" => Reg::S10,
            "s11" => Reg::S11,
            "s12" => Reg::S12,
            "s13" => Reg::S13,
            "s14" => Reg::S14,
            "s15" => Reg::S15,
            "s16" => Reg::S16,
            "s17" => Reg::S17,
            "s18" => Reg::S18,
            "s19" => Reg::S19,
            "s20" => Reg::S20,
            "s21" => Reg::S21,
            "s22" => Reg::S22,
            "s23" => Reg::S23,
            "t10" => Reg::T10,
            "t11" => Reg::T11,
            "t12" => Reg::T12,
            "t13" => Reg::T13,
            "t14" => Reg::T14,
            "t15" => Reg::T15,
            "t16" => Reg::T16,
            "t17" => Reg::T17,
            "t18" => Reg::T18,
            "t19" => Reg::T19,
            "t20" => Reg::T20,
            "t21" => Reg::T21,
            "t22" => Reg::T22,
            "t23" => Reg::T23,
            "t24" => Reg::T24,
            "t25" => Reg::T25,
            _ => match value.parse::<usize>() {
                Ok(n) if n < 64 => REGS[n],
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
            Reg::S8 => 32,
            Reg::S9 => 33,
            Reg::S10 => 34,
            Reg::S11 => 35,
            Reg::S12 => 36,
            Reg::S13 => 37,
            Reg::S14 => 38,
            Reg::S15 => 39,
            Reg::S16 => 40,
            Reg::S17 => 41,
            Reg::S18 => 42,
            Reg::S19 => 43,
            Reg::S20 => 44,
            Reg::S21 => 45,
            Reg::S22 => 46,
            Reg::S23 => 47,
            Reg::T10 => 48,
            Reg::T11 => 49,
            Reg::T12 => 50,
            Reg::T13 => 51,
            Reg::T14 => 52,
            Reg::T15 => 53,
            Reg::T16 => 54,
            Reg::T17 => 55,
            Reg::T18 => 56,
            Reg::T19 => 57,
            Reg::T20 => 58,
            Reg::T21 => 59,
            Reg::T22 => 60,
            Reg::T23 => 61,
            Reg::T24 => 62,
            Reg::T25 => 63,
        }
    }
}

impl From<Reg> for BF {
    fn from(value: Reg) -> Self {
        let n: u32 = value.into();
        n.into()
    }
}

impl From<&Reg> for BF {
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

impl From<&RegA> for BF {
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

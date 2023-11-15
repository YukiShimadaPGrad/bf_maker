//! 簡単にビットフラグを扱うツール

use std::ops::BitAnd;
use std::ops::BitOr;
use std::ops::BitXor;
use std::ops::Not;

pub trait BitFlag {
    /// `bit` をたてる
    fn on(&self, bit: usize) -> Self;

    /// `bit` を消す
    fn off(&self, bit: usize) -> Self;

    /// `bit` を切り替える
    fn toggle(&self, bit: usize) -> Self;

    /// `bit` がたっているか確認する
    fn get(&self, bit: usize) -> bool;

    /// いずれかのビットがたっているか確認する
    fn any(&self) -> bool;

    /// たっているビットの数を数える
    fn count(&self) -> u32;
}

#[derive(Clone, Copy, Hash, Debug, Default, PartialEq, Eq)]
pub struct U8Flag {
    flag: u8,
}

impl U8Flag {
    pub fn new(flag: u8) -> Self {
        U8Flag { flag }
    }

    pub fn get_raw(&self) -> u8 {
        self.flag
    }
}

impl From<u8> for U8Flag {
    fn from(value: u8) -> Self {
        Self::new(value)
    }
}

impl BitAnd for U8Flag {
    type Output = U8Flag;

    fn bitand(self, rhs: Self) -> Self::Output {
        (self.flag & rhs.flag).into()
    }
}

impl BitOr for U8Flag {
    type Output = U8Flag;

    fn bitor(self, rhs: Self) -> Self::Output {
        (self.flag | rhs.flag).into()
    }
}

impl BitXor for U8Flag {
    type Output = U8Flag;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (self.flag ^ rhs.flag).into()
    }
}

impl Not for U8Flag {
    type Output = U8Flag;

    fn not(self) -> Self::Output {
        (!self.flag).into()
    }
}

impl BitFlag for U8Flag {
    fn on(&self, bit: usize) -> Self {
        (self.flag | (1 << bit)).into()
    }

    fn off(&self, bit: usize) -> Self {
        (self.flag & (!(1 << bit))).into()
    }

    fn toggle(&self, bit: usize) -> Self {
        (self.flag ^ (1 << bit)).into()
    }

    fn get(&self, bit: usize) -> bool {
        (self.flag & (1 << bit)) != 0
    }

    fn any(&self) -> bool {
        self.flag != 0
    }

    fn count(&self) -> u32 {
        self.flag.count_ones()
    }
}

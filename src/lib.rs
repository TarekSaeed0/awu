#![no_std]

#[macro_export]
macro_rules! forward_ref_unop {
    (impl $($trait:ident)::+, $method:ident for $type:ty) => {
        impl $($trait)::+ for &$type {
            type Output = <$type as $($trait)::+>::Output;

            #[inline]
            fn $method(self) -> Self::Output {
                (*self).$method()
            }
        }
    };
}

#[macro_export]
macro_rules! forward_ref_binop {
    (impl $($trait:ident)::+<$rhs_type:ty>, $method:ident for $type:ty) => {
        impl $($trait)::+<$rhs_type> for &$type {
            type Output = <$type as $($trait)::+<$rhs_type>>::Output;

            #[inline]
            fn $method(self, rhs: $rhs_type) -> Self::Output {
                (*self).$method(rhs)
            }
        }

        impl $($trait)::+<&$rhs_type> for $type {
            type Output = <$type as $($trait)::+<$rhs_type>>::Output;

            #[inline]
            fn $method(self, rhs: &$rhs_type) -> Self::Output {
                self.$method(*rhs)
            }
        }

        impl $($trait)::+<&$rhs_type> for &$type {
            type Output = <$type as $($trait)::+<$rhs_type>>::Output;

            #[inline]
            fn $method(self, rhs: &$rhs_type) -> Self::Output {
                (*self).$method(*rhs)
            }
        }
    };
    (impl $($trait:ident)::+, $method:ident for $type:ty) => {
        un::forward_ref_binop! {impl $($trait)::+<$type>, $method for $type }
    };
}

#[macro_export]
macro_rules! forward_ref_op_assign {
    (impl $($trait:ident)::+<$rhs_type:ty>, $method:ident for $type:ty) => {
        impl $($trait)::+<&$rhs_type> for $type {
            #[inline]
            fn $method(&mut self, rhs: &$rhs_type) {
                self.$method(*rhs)
            }
        }
    };
    (impl $($trait:ident)::+, $method:ident for $type:ty) => {
        un::forward_ref_op_assign! {impl $($trait)::+<$type>, $method for $type }
    };
}

#[macro_export]
macro_rules! impl_op_assign {
    (impl $($trait1:ident)::+<$rhs_type1:ty>, $method1:ident use $($trait2:ident)::+<$rhs_type2:ty>, $method2:ident for $type:ty) => {
        impl $($trait1)::+<$rhs_type1> for $type {
            #[inline]
            fn $method1(&mut self, rhs: $rhs_type1) { 
                *self = $($trait2)::+::<$rhs_type2>::$method2(&*self, rhs);
            }
        }
        un::forward_ref_op_assign! { impl $($trait1)::+<$rhs_type1>, $method1 for $type }
    };
    (impl $($trait1:ident)::+, $method1:ident use $($trait2:ident)::+<$rhs_type2:ty>, $method2:ident for $type:ty) => {
        un::impl_op_assign! {impl $($trait1)::+<$type>, $method1 use $($trait2)::+<$rhs_type2>, $method2 for $type }
    };
    (impl $($trait1:ident)::+<$rhs_type1:ty>, $method1:ident use $($trait2:ident)::+, $method2:ident for $type:ty) => {
        un::impl_op_assign! {impl $($trait1)::+<$rhs_type1>, $method1 use $($trait2)::+<$type>, $method2 for $type }
    };
    (impl $($trait1:ident)::+, $method1:ident use $($trait2:ident)::+, $method2:ident for $type:ty) => {
        un::impl_op_assign! {impl $($trait1)::+<$type>, $method1 use $($trait2)::+<$type>, $method2 for $type }
    };
}

#[macro_export]
macro_rules! impl_binop {
    (impl $($trait:ident)::+, $method:ident for $type:ty, $msg:tt) => {
        impl $($trait)::+ for $type {
            type Output = Self;

            #[inline]
            fn $method(self, rhs: Self) -> Self::Output {
                let x = self.0.$method(rhs.0);
                debug_assert!(x <= Self::MAX.0, $msg);
                Self::wrapping_new(x)
            }
        }

        un::forward_ref_binop! { impl $($trait)::+, $method for $type }
    };
    (impl $($trait:ident)::+, $method:ident for $type:ty) => {
        impl $($trait)::+ for $type {
            type Output = Self;

            #[inline]
            fn $method(self, rhs: Self) -> Self::Output {
                Self(self.0.$method(rhs.0))
            }
        }

        un::forward_ref_binop! { impl $($trait)::+, $method for $type }
    };
}

#[macro_export]
macro_rules! impl_shift {
    (impl $($trait:ident)::+<$rhs_type:ty>, $method:ident for $type:ty, $msg:tt) => {
        impl $($trait)::+<$rhs_type> for $type {
            type Output = Self;

            #[inline]
            fn $method(self, rhs: $rhs_type) -> Self::Output {
                debug_assert!(u32::try_from(rhs).map_or(false, |x| x <= Self::BITS), $msg);
                Self::wrapping_new(self.0.$method(<$rhs_type>::try_from(Self::BITS).map_or(rhs, |x| rhs % x)))

            }
        }

        un::forward_ref_binop! { impl $($trait)::+<$rhs_type>, $method for $type }
    };
}

#[macro_export]
macro_rules! impl_fmt {
    (impl $($trait:ident)::* for $type:ty) => {      
        impl $($trait)::* for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result { 
                self.0.fmt(f)
            }
        }
    };
}

#[macro_export]
macro_rules! def_uint {
    (
        $(#[$attr:meta])* 
        $vis:vis struct $name:ident($type:ty) where BITS: $bits:expr;
    ) => {
        $(#[$attr])*
        #[repr(transparent)]
        #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        $vis struct $name($type);
        impl $name {
            pub const MIN: Self = Self(0);
            pub const MAX: Self = Self((1 << Self::BITS) - 1);
            pub const BITS: u32 = $bits;

            #[inline]
            pub const fn new(value: $type) -> Self {
                debug_assert!(value <= Self::MAX.0, concat!("attemp to create ", stringify!($name), " with overflow"));
                Self::wrapping_new(value)
            }

            #[inline]
            pub const fn checked_new(value: $type) -> Option<Self> {
                if value <= Self::MAX.0 {Some(Self(value))} else {None}
            }

            #[inline]
            pub const fn saturating_new(value: $type) -> Self {
                if value <= Self::MAX.0 {Self(value)} else {Self::MAX}
            }

            #[inline]
            pub const fn wrapping_new(value: $type) -> Self {
                Self(value & Self::MAX.0)
            }

            #[inline]
            pub const fn overflowing_new(value: $type) -> (Self, bool) {
                (Self::wrapping_new(value), value > Self::MAX.0)
            }

            //from_str_radix not currently supported

            #[inline]
            pub const fn count_ones(self) -> u32 {
                self.0.count_ones()
            }

            #[inline]
            pub const fn count_zeros(self) -> u32 {
                self.0.count_zeros() - (<$type>::BITS - Self::BITS)
            }

            #[inline]
            pub const fn leading_zeros(self) -> u32 {
                self.0.leading_zeros() - (<$type>::BITS - Self::BITS)
            }

            #[inline]
            pub const fn trailing_zeros(self) -> u32 {
                match self.0.trailing_zeros() {
                    x if x > Self::BITS => Self::BITS,
                    x => x,
                }
            }

            #[inline]
            pub const fn leading_ones(self) -> u32 {
                (self.0 << (<$type>::BITS - Self::BITS)).leading_ones()
            }

            #[inline]
            pub const fn trailing_ones(self) -> u32 {
                self.0.trailing_ones()
            }

            #[inline]
            pub const fn rotate_left(self, n: u32) -> Self {
                Self::wrapping_new(self.0 << (n % Self::BITS) | self.0 >> (Self::BITS - (n % Self::BITS)))
            }

            #[inline]
            pub const fn rotate_right(self, n: u32) -> Self {
                Self::wrapping_new(self.0 >> (n % Self::BITS) | self.0 << (Self::BITS - (n % Self::BITS)))
            }

            #[inline]
            pub const fn reverse_bits(self) -> Self {
                Self::wrapping_new(self.0.reverse_bits() >> (<$type>::BITS - Self::BITS))
            }

            #[inline]
            pub const fn checked_add(self, rhs: Self) -> Option<Self> {
                let (a, b) = self.overflowing_add(rhs);
                if b {None} else {Some(a)}
            }

            #[inline]
            pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
                let (a, b) = self.overflowing_sub(rhs);
                if b {None} else {Some(a)}
            }

            #[inline]
            pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
                let (a, b) = self.overflowing_mul(rhs);
                if b {None} else {Some(a)}
            }

            #[inline]
            pub const fn checked_div(self, rhs: Self) -> Option<Self> {
                match self.0.checked_div(rhs.0) {
                    Some(x) => Some(Self(x)),
                    None => None,
                }
            }

            #[inline]
            pub const fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
                match self.0.checked_div_euclid(rhs.0) {
                    Some(x) => Some(Self(x)),
                    None => None,
                }
            }
            
            #[inline]
            pub const fn checked_rem(self, rhs: Self) -> Option<Self> {
                match self.0.checked_rem(rhs.0) {
                    Some(x) => Some(Self(x)),
                    None => None,
                }
            }

            #[inline]
            pub const fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
                match self.0.checked_rem_euclid(rhs.0) {
                    Some(x) => Some(Self(x)),
                    None => None,
                }
            }

            #[inline]
            pub const fn checked_neg(self) -> Option<Self> {
                let (a, b) = self.overflowing_neg();
                if b {None} else {Some(a)}
            }

            #[inline]
            pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
                let (a, b) = self.overflowing_shl(rhs);
                if b {None} else {Some(a)}
            }

            #[inline]
            pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
                let (a, b) = self.overflowing_shr(rhs);
                if b {None} else {Some(a)}
            }

            #[inline]
            pub const fn checked_pow(self, mut exp: u32) -> Option<Self> {
                if exp == 0 {
                    return Some(Self(1));
                }
                let mut base = self;
                let mut acc = Self(1);
    
                while exp > 1 {
                    if (exp & 1) == 1 {
                        acc = match acc.checked_mul(base) {
                            Some(x) => x,
                            None => return None,
                        };
                    }
                    exp /= 2;
                    base = match base.checked_mul(base) {
                        Some(x) => x,
                        None => return None,
                    };
                }
    
                Some(match acc.checked_mul(base) {
                    Some(x) => x,
                    None => return None,
                })
            }

            #[inline]
            pub const fn saturating_add(self, rhs: Self) -> Self {
                match self.0.saturating_add(rhs.0) {
                    x if x > Self::MAX.0 => Self::MAX,
                    x => Self(x),
                }
            }

            #[inline]
            pub const fn saturating_sub(self, rhs: Self) -> Self {
                Self(self.0.saturating_sub(rhs.0))
            }

            #[inline]
            pub const fn saturating_mul(self, rhs: Self) -> Self {
                match self.checked_mul(rhs) {
                    Some(x) => x,
                    None => Self::MAX,
                }
            }

            #[inline]
            pub const fn saturating_div(self, rhs: Self) -> Self {
                self.wrapping_div(rhs)
            }

            #[inline]
            pub const fn saturating_pow(self, exp: u32) -> Self {
                match self.checked_pow(exp) {
                    Some(x) => x,
                    None => Self::MAX,
                }
            }

            #[inline]
            pub const fn wrapping_add(self, rhs: Self) -> Self {
                Self::wrapping_new(self.0.wrapping_add(rhs.0))
            }

            #[inline]
            pub const fn wrapping_sub(self, rhs: Self) -> Self {
                Self::wrapping_new(self.0.wrapping_sub(rhs.0))
            }

            #[inline]
            pub const fn wrapping_mul(self, rhs: Self) -> Self {
                Self::wrapping_new(self.0.wrapping_mul(rhs.0))
            }

            #[inline]
            pub const fn wrapping_div(self, rhs: Self) -> Self {
                Self(self.0.wrapping_div(rhs.0))
            }

            #[inline]
            pub const fn wrapping_div_euclid(self, rhs: Self) -> Self {
                Self(self.0.wrapping_div_euclid(rhs.0))
            }

            #[inline]
            pub const fn wrapping_rem(self, rhs: Self) -> Self {
                Self(self.0.wrapping_rem(rhs.0))
            }

            #[inline]
            pub const fn wrapping_rem_euclid(self, rhs: Self) -> Self {
                Self(self.0.wrapping_rem_euclid(rhs.0))
            }

            #[inline]
            pub const fn wrapping_neg(self) -> Self {
                Self::wrapping_new(self.0.wrapping_neg())
            }

            #[inline]
            pub const fn wrapping_shl(self, rhs: u32) -> Self {
                Self::wrapping_new(self.0.wrapping_shl(rhs % Self::BITS))
            }

            #[inline]
            pub const fn wrapping_shr(self, rhs: u32) -> Self {
                Self::wrapping_new(self.0.wrapping_shr(rhs % Self::BITS))
            }

            #[inline]
            pub const fn wrapping_pow(self, exp: u32) -> Self {
                Self::wrapping_new(self.0.wrapping_pow(exp))
            }

            #[inline]
            pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_add(rhs.0);
                (Self::wrapping_new(a), b || a > Self::MAX.0)
            }

            #[inline]
            pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_sub(rhs.0);
                (Self::wrapping_new(a), b)
            }

            #[inline]
            pub const fn abs_diff(self, other: Self) -> Self {
                Self(self.0.abs_diff(other.0))
            }

            #[inline]
            pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_mul(rhs.0);
                (Self::wrapping_new(a), b || a > Self::MAX.0)
            }

            #[inline]
            pub const fn overflowing_div(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_div(rhs.0);
                (Self(a), b)
            }

            #[inline]
            pub const fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_div_euclid(rhs.0);
                (Self(a), b)
            }

            #[inline]
            pub const fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_rem(rhs.0);
                (Self(a), b)
            }

            #[inline]
            pub const fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_rem_euclid(rhs.0);
                (Self(a), b)
            }
            
            #[inline]
            pub const fn overflowing_neg(self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_neg();
                (Self::wrapping_new(a), b)
            }

            #[inline]
            pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
                let (a, b) = self.0.overflowing_shl(rhs % Self::BITS);
                (Self::wrapping_new(a), b || (rhs >= Self::BITS))
            }

            #[inline]
            pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
                let (a, b) = self.0.overflowing_shr(rhs % Self::BITS);
                (Self::wrapping_new(a), b || (rhs >= Self::BITS))
            }

            #[inline]
            pub const fn overflowing_pow(self, exp: u32) -> (Self, bool) {
                let (a, b) = self.0.overflowing_pow(exp);
                (Self::wrapping_new(a), b || a > Self::MAX.0)
            }

            #[inline]
            pub const fn pow(self, exp: u32) -> Self {
                let x = self.0.pow(exp);
                debug_assert!(x <= Self::MAX.0, "attempt to multiply with overflow");
                Self::wrapping_new(x)
            }

            #[inline]
            pub const fn div_euclid(self, rhs: Self) -> Self {
                Self(self.0.div_euclid(rhs.0))
            }

            #[inline]
            pub const fn rem_euclid(self, rhs: Self) -> Self {
                Self(self.0.rem_euclid(rhs.0))
            }

            #[inline]
            pub const fn is_power_of_two(self) -> bool {
                self.0.is_power_of_two()
            }

            #[inline]
            const fn next_power_of_two(self) -> Self {
                let x = self.0.next_power_of_two();
                debug_assert!(x <= Self::MAX.0, "attempt to add with overflow");
                Self::wrapping_new(x)
            }

            #[inline]
            const fn checked_next_power_of_two(self) -> Option<Self> {
                match self.0.checked_next_power_of_two() {
                    Some(x) if x <= Self::MAX.0 => Some(Self(x)),
                    _ => None,
                }
            }
        }

        un::impl_fmt! { impl core::fmt::Display for $name }

        un::impl_fmt! { impl core::fmt::Binary for $name }

        un::impl_fmt! { impl core::fmt::Octal for $name }

        un::impl_fmt! { impl core::fmt::UpperHex for $name }

        un::impl_fmt! { impl core::fmt::LowerHex for $name }

        un::impl_binop! { impl core::ops::Add, add for $name, "attempt to add with overflow" }

        un::impl_binop! { impl core::ops::Sub, sub for $name }

        un::impl_binop! { impl core::ops::Mul, mul for $name, "attempt to multiply with overflow" }

        un::impl_binop! { impl core::ops::Div, div for $name }

        un::impl_binop! { impl core::ops::Rem, rem  for $name }
  
        un::impl_binop! { impl core::ops::BitAnd, bitand for $name }

        un::impl_binop! { impl core::ops::BitOr, bitor for $name }

        un::impl_binop! { impl core::ops::BitXor, bitxor for $name }

        un::impl_shift! { impl core::ops::Shl<u8>, shl for $name, "attempt to shift left with overflow" }
        
        un::impl_shift! { impl core::ops::Shl<u16>, shl for $name, "attempt to shift left with overflow" }

        un::impl_shift! { impl core::ops::Shl<u32>, shl for $name, "attempt to shift left with overflow" }

        un::impl_shift! { impl core::ops::Shl<u64>, shl for $name, "attempt to shift left with overflow" }

        #[cfg(has_u128)]
        un::impl_shift! { impl core::ops::Shl<u128>, shl for $name, "attempt to shift left with overflow" }

        un::impl_shift! { impl core::ops::Shl<usize>, shl for $name, "attempt to shift left with overflow" }

        un::impl_shift! { impl core::ops::Shl<i8>, shl for $name, "attempt to shift left with overflow" }
        
        un::impl_shift! { impl core::ops::Shl<i16>, shl for $name, "attempt to shift left with overflow" }

        un::impl_shift! { impl core::ops::Shl<i32>, shl for $name, "attempt to shift left with overflow" }

        un::impl_shift! { impl core::ops::Shl<i64>, shl for $name, "attempt to shift left with overflow" }

        #[cfg(has_i128)]
        un::impl_shift! { impl core::ops::Shl<i128>, shl for $name, "attempt to shift left with overflow" }

        un::impl_shift! { impl core::ops::Shl<isize>, shl for $name, "attempt to shift left with overflow" }

        un::impl_shift! { impl core::ops::Shr<u8>, shr for $name, "attempt to shift right with overflow" }
        
        un::impl_shift! { impl core::ops::Shr<u16>, shr for $name, "attempt to shift right with overflow" }

        un::impl_shift! { impl core::ops::Shr<u32>, shr for $name, "attempt to shift right with overflow" }

        un::impl_shift! { impl core::ops::Shr<u64>, shr for $name, "attempt to shift right with overflow" }

        #[cfg(has_u128)]
        un::impl_shift! { impl core::ops::Shr<u128>, shr for $name, "attempt to shift right with overflow" }

        un::impl_shift! { impl core::ops::Shr<usize>, shr for $name, "attempt to shift right with overflow" }

        un::impl_shift! { impl core::ops::Shr<i8>, shr for $name, "attempt to shift right with overflow" }
        
        un::impl_shift! { impl core::ops::Shr<i16>, shr for $name, "attempt to shift right with overflow" }

        un::impl_shift! { impl core::ops::Shr<i32>, shr for $name, "attempt to shift right with overflow" }

        un::impl_shift! { impl core::ops::Shr<i64>, shr for $name, "attempt to shift right with overflow" }

        #[cfg(has_i128)]
        un::impl_shift! { impl core::ops::Shr<i128>, shr for $name, "attempt to shift right with overflow" }

        un::impl_shift! { impl core::ops::Shr<isize>, shr for $name, "attempt to shift right with overflow" }

        un::impl_op_assign! { impl core::ops::AddAssign, add_assign use core::ops::Add, add for $name }

        un::impl_op_assign! { impl core::ops::SubAssign, sub_assign use core::ops::Sub, sub for $name }

        un::impl_op_assign! { impl core::ops::MulAssign, mul_assign use core::ops::Mul, mul for $name }

        un::impl_op_assign! { impl core::ops::DivAssign, div_assign use core::ops::Div, div for $name }

        un::impl_op_assign! { impl core::ops::RemAssign, rem_assign use core::ops::Rem, rem for $name }

        un::impl_op_assign! { impl core::ops::BitAndAssign, bitand_assign use core::ops::BitAnd, bitand for $name }

        un::impl_op_assign! { impl core::ops::BitOrAssign, bitor_assign use core::ops::BitOr, bitor for $name }

        un::impl_op_assign! { impl core::ops::BitXorAssign, bitxor_assign use core::ops::BitXor, bitxor for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<u8>, shl_assign use core::ops::Shl<u8>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<u16>, shl_assign use core::ops::Shl<u16>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<u32>, shl_assign use core::ops::Shl<u32>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<u64>, shl_assign use core::ops::Shl<u64>, shl for $name }

        #[cfg(has_u128)]
        un::impl_op_assign! { impl core::ops::ShlAssign<u128>, shl_assign use core::ops::Shl<u128>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<usize>, shl_assign use core::ops::Shl<usize>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<i8>, shl_assign use core::ops::Shl<i8>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<i16>, shl_assign use core::ops::Shl<i16>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<i32>, shl_assign use core::ops::Shl<i32>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<i64>, shl_assign use core::ops::Shl<i64>, shl for $name }

        #[cfg(has_i128)]
        un::impl_op_assign! { impl core::ops::ShlAssign<i128>, shl_assign use core::ops::Shl<i128>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShlAssign<isize>, shl_assign use core::ops::Shl<isize>, shl for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<u8>, shr_assign use core::ops::Shr<u8>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<u16>, shr_assign use core::ops::Shr<u16>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<u32>, shr_assign use core::ops::Shr<u32>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<u64>, shr_assign use core::ops::Shr<u64>, shr for $name }

        #[cfg(has_u128)]
        un::impl_op_assign! { impl core::ops::ShrAssign<u128>, shr_assign use core::ops::Shr<u128>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<usize>, shr_assign use core::ops::Shr<usize>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<i8>, shr_assign use core::ops::Shr<i8>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<i16>, shr_assign use core::ops::Shr<i16>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<i32>, shr_assign use core::ops::Shr<i32>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<i64>, shr_assign use core::ops::Shr<i64>, shr for $name }

        #[cfg(has_i128)]
        un::impl_op_assign! { impl core::ops::ShrAssign<i128>, shr_assign use core::ops::Shr<i128>, shr for $name }

        un::impl_op_assign! { impl core::ops::ShrAssign<isize>, shr_assign use core::ops::Shr<isize>, shr for $name }
    };
}
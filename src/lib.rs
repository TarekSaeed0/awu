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
        awu::forward_ref_binop! {impl $($trait)::+<$type>, $method for $type }
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
        awu::forward_ref_op_assign! {impl $($trait)::+<$type>, $method for $type }
    };
}

#[macro_export]
macro_rules! impl_fmt {
    (impl $($trait:ident)::+ for $type:ty) => {
        impl $($trait)::+ for $type {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                $($trait)::+::fmt(&self.0, f)
            }
        }
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

        awu::forward_ref_binop! { impl $($trait)::+, $method for $type }
    };
    (impl $($trait:ident)::+, $method:ident for $type:ty) => {
        impl $($trait)::+ for $type {
            type Output = Self;

            #[inline]
            fn $method(self, rhs: Self) -> Self::Output {
                Self(self.0.$method(rhs.0))
            }
        }

        awu::forward_ref_binop! { impl $($trait)::+, $method for $type }
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
        awu::forward_ref_op_assign! { impl $($trait1)::+<$rhs_type1>, $method1 for $type }
    };
    (impl $($trait1:ident)::+, $method1:ident use $($trait2:ident)::+<$rhs_type2:ty>, $method2:ident for $type:ty) => {
        awu::impl_op_assign! {impl $($trait1)::+<$type>, $method1 use $($trait2)::+<$rhs_type2>, $method2 for $type }
    };
    (impl $($trait1:ident)::+<$rhs_type1:ty>, $method1:ident use $($trait2:ident)::+, $method2:ident for $type:ty) => {
        awu::impl_op_assign! {impl $($trait1)::+<$rhs_type1>, $method1 use $($trait2)::+<$type>, $method2 for $type }
    };
    (impl $($trait1:ident)::+, $method1:ident use $($trait2:ident)::+, $method2:ident for $type:ty) => {
        awu::impl_op_assign! {impl $($trait1)::+<$type>, $method1 use $($trait2)::+<$type>, $method2 for $type }
    };
}

#[macro_export]
macro_rules! impl_shift {
    (impl $($trait:ident)::+<$rhs_type:ty>, $method:ident for $type:ty, $msg:tt) => {
        impl $($trait)::+<$rhs_type> for $type {
            type Output = Self;

            #[inline]
            fn $method(self, rhs: $rhs_type) -> Self::Output {
                debug_assert!(u32::try_from(rhs).map_or(false, |x| x < Self::BITS), $msg);
                Self::wrapping_new(self.0.$method(<$rhs_type>::try_from(Self::BITS).map_or(rhs, |x| rhs % x)))

            }
        }

        awu::forward_ref_binop! { impl $($trait)::+<$rhs_type>, $method for $type }
    };
    (impl $($trait:ident)::+, $method:ident for $type:ty, $msg:tt) => {
        awu::impl_shift! { impl $($trait)::+<$type>, $method for $type, $msg }
    }
}

#[macro_export]
macro_rules! impl_from {
    (impl $($trait:ident)::+<$value_type:ty>, $method:ident for $type:ty) => {
        impl $($trait)::+<$value_type> for $type {
            #[inline]
            fn $method(value: $value_type) -> Self {
                Self::checked_new(value.into()).expect(concat!(" From<", stringify!($value_type), "> for ", stringify!($type), " isn't infallible, consider implementing it as TryFrom instead"))
            }
        }
    };
}

#[macro_export]
macro_rules! impl_try_from {
    (impl $($trait:ident)::+<$value_type:ty>, $method:ident for $type:ty where INNER: $inner_type:ty) => {
        impl $($trait)::+<$value_type> for $type {
            type Error = Option<<$inner_type as $($trait)::+<$value_type>>::Error>;

            #[inline]
            fn $method(value: $value_type) -> Result<Self, Self::Error> {
                Self::checked_new(value.try_into()?).ok_or(None)
            }
        }
    };
}

#[macro_export]
macro_rules! impl_into {
    (impl $($trait:ident)::+<$value_type:ty>, $method:ident for $type:ty) => {
        impl $($trait)::+<$value_type> for $type {
            #[inline]
            fn $method(value: $value_type) -> Self {
                value.0.into()
            }
        }
    };
}

#[macro_export]
macro_rules! impl_try_into {
    (impl $($trait:ident)::+<$value_type:ty where INNER: $inner_type:ty>, $method:ident for $type:ty) => {
        impl $($trait)::+<$value_type> for $type {
            type Error = <$type as $($trait)::+<$inner_type>>::Error;

            #[inline]
            fn $method(value: $value_type) -> Result<Self, Self::Error> {
                value.0.try_into()
            }
        }
    };
}

#[macro_export]
macro_rules! def_awu {
    (
        $(#[$attr:meta])*
        $vis:vis struct $type:ident($inner_type:ty)
        where
            BITS: $bits:expr$(,
            FROM: [$($($from_types:ty),+$(,)?)?])?$(,
            TRY_FROM: [$($($try_from_types:ty),+$(,)?)?])?$(,
            INTO: [$($($into_types:ty),+$(,)?)?])?$(,
            TRY_INTO: [$($($try_into_types:ty),+$(,)?)?])?$(,)?
        ;

        $(
            $(#[$macro_attr:meta])*
            macro $macro_name:ident;
        )?
    ) => {
        $(
            $(#[$macro_attr])*
            macro_rules! $macro_name {
                ($value:expr) => { $type::new($value) };
            }
        )?

        $(#[$attr])*
        #[repr(transparent)]
        #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        $vis struct $type($inner_type);
        impl $type {
            pub const MIN: Self = Self(0);
            pub const MAX: Self = Self((1 << Self::BITS) - 1);
            pub const BITS: u32 = $bits;

            #[inline]
            pub const fn new(value: $inner_type) -> Self {
                debug_assert!(value <= Self::MAX.0, concat!("attempt to create ", stringify!($type), " with overflow"));
                Self::wrapping_new(value)
            }

            #[inline]
            pub const fn checked_new(value: $inner_type) -> Option<Self> {
                if value <= Self::MAX.0 {Some(Self(value))} else {None}
            }

            #[inline]
            pub const fn saturating_new(value: $inner_type) -> Self {
                if value <= Self::MAX.0 {Self(value)} else {Self::MAX}
            }

            #[inline]
            pub const fn wrapping_new(value: $inner_type) -> Self {
                Self(value & Self::MAX.0)
            }

            #[inline]
            pub const fn overflowing_new(value: $inner_type) -> (Self, bool) {
                (Self::wrapping_new(value), value > Self::MAX.0)
            }

            #[inline]
            pub const fn into_inner(self) -> $inner_type {
                self.0
            }

            #[inline]
            pub fn from_str_radix(src: &str, radix: u32) -> Result<Self, Option<core::num::ParseIntError>> {
                Self::checked_new(<$inner_type>::from_str_radix(src, radix)?).ok_or(None)
            }

            #[inline]
            pub const fn count_ones(self) -> u32 {
                self.0.count_ones()
            }

            #[inline]
            pub const fn count_zeros(self) -> u32 {
                self.0.count_zeros() - (<$inner_type>::BITS - Self::BITS)
            }

            #[inline]
            pub const fn leading_zeros(self) -> u32 {
                self.0.leading_zeros() - (<$inner_type>::BITS - Self::BITS)
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
                (self.0 << (<$inner_type>::BITS - Self::BITS)).leading_ones()
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
                Self::wrapping_new(self.0.reverse_bits() >> (<$inner_type>::BITS - Self::BITS))
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
                Self::saturating_new(self.0.saturating_add(rhs.0))
            }

            #[inline]
            pub const fn saturating_sub(self, rhs: Self) -> Self {
                Self(self.0.saturating_sub(rhs.0))
            }

            #[inline]
            pub const fn saturating_mul(self, rhs: Self) -> Self {
                Self::saturating_new(self.0.saturating_mul(rhs.0))
            }

            #[inline]
            pub const fn saturating_div(self, rhs: Self) -> Self {
                Self(self.0.saturating_div(rhs.0))
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
            pub const fn next_power_of_two(self) -> Self {
                let x = self.0.next_power_of_two();
                debug_assert!(x <= Self::MAX.0, "attempt to add with overflow");
                Self::wrapping_new(x)
            }

            #[inline]
            pub const fn checked_next_power_of_two(self) -> Option<Self> {
                match self.0.checked_next_power_of_two() {
                    Some(x) if x <= Self::MAX.0 => Some(Self(x)),
                    _ => None,
                }
            }
        }

        awu::impl_fmt! { impl core::fmt::Display for $type }
        awu::impl_fmt! { impl core::fmt::Binary for $type }
        awu::impl_fmt! { impl core::fmt::Octal for $type }
        awu::impl_fmt! { impl core::fmt::LowerHex for $type }
        awu::impl_fmt! { impl core::fmt::UpperHex for $type }
        awu::impl_fmt! { impl core::fmt::LowerExp for $type }
        awu::impl_fmt! { impl core::fmt::UpperExp for $type }

        awu::impl_binop! { impl core::ops::Add, add for $type, "attempt to add with overflow" }
        awu::impl_binop! { impl core::ops::Sub, sub for $type }
        awu::impl_binop! { impl core::ops::Mul, mul for $type, "attempt to multiply with overflow" }
        awu::impl_binop! { impl core::ops::Div, div for $type }
        awu::impl_binop! { impl core::ops::Rem, rem  for $type }

        impl core::ops::Not for $type {
            type Output = Self;

            #[inline]
            fn not(self) -> Self {
                Self::wrapping_new(!self.0)
            }
        }

        awu::forward_ref_unop! { impl core::ops::Not, not for $type }

        awu::impl_binop! { impl core::ops::BitAnd, bitand for $type }
        awu::impl_binop! { impl core::ops::BitOr, bitor for $type }
        awu::impl_binop! { impl core::ops::BitXor, bitxor for $type }

       impl core::ops::Shl for $type {
           type Output = Self;

            #[inline]
            fn shl(self, rhs: Self) -> Self::Output {
                self << rhs.0
            }
        }

        awu::forward_ref_binop! { impl core::ops::Shl, shl for $type }

        awu::impl_shift! { impl core::ops::Shl<u8>, shl for $type, "attempt to shift left with overflow" }
        awu::impl_shift! { impl core::ops::Shl<u16>, shl for $type, "attempt to shift left with overflow" }
        awu::impl_shift! { impl core::ops::Shl<u32>, shl for $type, "attempt to shift left with overflow" }
        awu::impl_shift! { impl core::ops::Shl<u64>, shl for $type, "attempt to shift left with overflow" }
        #[cfg(has_u128)]
        awu::impl_shift! { impl core::ops::Shl<u128>, shl for $type, "attempt to shift left with overflow" }
        awu::impl_shift! { impl core::ops::Shl<usize>, shl for $type, "attempt to shift left with overflow" }

        awu::impl_shift! { impl core::ops::Shl<i8>, shl for $type, "attempt to shift left with overflow" }
        awu::impl_shift! { impl core::ops::Shl<i16>, shl for $type, "attempt to shift left with overflow" }
        awu::impl_shift! { impl core::ops::Shl<i32>, shl for $type, "attempt to shift left with overflow" }
        awu::impl_shift! { impl core::ops::Shl<i64>, shl for $type, "attempt to shift left with overflow" }
        #[cfg(has_i128)]
        awu::impl_shift! { impl core::ops::Shl<i128>, shl for $type, "attempt to shift left with overflow" }
        awu::impl_shift! { impl core::ops::Shl<isize>, shl for $type, "attempt to shift left with overflow" }

        impl core::ops::Shr for $type {
            type Output = Self;

            #[inline]
            fn shr(self, rhs: Self) -> Self::Output {
                self >> rhs.0
            }
        }

         awu::forward_ref_binop! { impl core::ops::Shr, shr for $type }

        awu::impl_shift! { impl core::ops::Shr<u8>, shr for $type, "attempt to shift right with overflow" }
        awu::impl_shift! { impl core::ops::Shr<u16>, shr for $type, "attempt to shift right with overflow" }
        awu::impl_shift! { impl core::ops::Shr<u32>, shr for $type, "attempt to shift right with overflow" }
        awu::impl_shift! { impl core::ops::Shr<u64>, shr for $type, "attempt to shift right with overflow" }
        #[cfg(has_u128)]
        awu::impl_shift! { impl core::ops::Shr<u128>, shr for $type, "attempt to shift right with overflow" }
        awu::impl_shift! { impl core::ops::Shr<usize>, shr for $type, "attempt to shift right with overflow" }

        awu::impl_shift! { impl core::ops::Shr<i8>, shr for $type, "attempt to shift right with overflow" }
        awu::impl_shift! { impl core::ops::Shr<i16>, shr for $type, "attempt to shift right with overflow" }
        awu::impl_shift! { impl core::ops::Shr<i32>, shr for $type, "attempt to shift right with overflow" }
        awu::impl_shift! { impl core::ops::Shr<i64>, shr for $type, "attempt to shift right with overflow" }
        #[cfg(has_i128)]
        awu::impl_shift! { impl core::ops::Shr<i128>, shr for $type, "attempt to shift right with overflow" }
        awu::impl_shift! { impl core::ops::Shr<isize>, shr for $type, "attempt to shift right with overflow" }

        awu::impl_op_assign! { impl core::ops::AddAssign, add_assign use core::ops::Add, add for $type }
        awu::impl_op_assign! { impl core::ops::SubAssign, sub_assign use core::ops::Sub, sub for $type }
        awu::impl_op_assign! { impl core::ops::MulAssign, mul_assign use core::ops::Mul, mul for $type }
        awu::impl_op_assign! { impl core::ops::DivAssign, div_assign use core::ops::Div, div for $type }
        awu::impl_op_assign! { impl core::ops::RemAssign, rem_assign use core::ops::Rem, rem for $type }

        awu::impl_op_assign! { impl core::ops::BitAndAssign, bitand_assign use core::ops::BitAnd, bitand for $type }
        awu::impl_op_assign! { impl core::ops::BitOrAssign, bitor_assign use core::ops::BitOr, bitor for $type }
        awu::impl_op_assign! { impl core::ops::BitXorAssign, bitxor_assign use core::ops::BitXor, bitxor for $type }

        awu::impl_op_assign! { impl core::ops::ShlAssign, shl_assign use core::ops::Shl, shl for $type }

        awu::impl_op_assign! { impl core::ops::ShlAssign<u8>, shl_assign use core::ops::Shl<u8>, shl for $type }
        awu::impl_op_assign! { impl core::ops::ShlAssign<u16>, shl_assign use core::ops::Shl<u16>, shl for $type }
        awu::impl_op_assign! { impl core::ops::ShlAssign<u32>, shl_assign use core::ops::Shl<u32>, shl for $type }
        awu::impl_op_assign! { impl core::ops::ShlAssign<u64>, shl_assign use core::ops::Shl<u64>, shl for $type }
        #[cfg(has_u128)]
        awu::impl_op_assign! { impl core::ops::ShlAssign<u128>, shl_assign use core::ops::Shl<u128>, shl for $type }
        awu::impl_op_assign! { impl core::ops::ShlAssign<usize>, shl_assign use core::ops::Shl<usize>, shl for $type }

        awu::impl_op_assign! { impl core::ops::ShlAssign<i8>, shl_assign use core::ops::Shl<i8>, shl for $type }
        awu::impl_op_assign! { impl core::ops::ShlAssign<i16>, shl_assign use core::ops::Shl<i16>, shl for $type }
        awu::impl_op_assign! { impl core::ops::ShlAssign<i32>, shl_assign use core::ops::Shl<i32>, shl for $type }
        awu::impl_op_assign! { impl core::ops::ShlAssign<i64>, shl_assign use core::ops::Shl<i64>, shl for $type }
        #[cfg(has_i128)]
        awu::impl_op_assign! { impl core::ops::ShlAssign<i128>, shl_assign use core::ops::Shl<i128>, shl for $type }
        awu::impl_op_assign! { impl core::ops::ShlAssign<isize>, shl_assign use core::ops::Shl<isize>, shl for $type }

        awu::impl_op_assign! { impl core::ops::ShrAssign, shr_assign use core::ops::Shr, shr for $type }

        awu::impl_op_assign! { impl core::ops::ShrAssign<u8>, shr_assign use core::ops::Shr<u8>, shr for $type }
        awu::impl_op_assign! { impl core::ops::ShrAssign<u16>, shr_assign use core::ops::Shr<u16>, shr for $type }
        awu::impl_op_assign! { impl core::ops::ShrAssign<u32>, shr_assign use core::ops::Shr<u32>, shr for $type }
        awu::impl_op_assign! { impl core::ops::ShrAssign<u64>, shr_assign use core::ops::Shr<u64>, shr for $type }
        #[cfg(has_u128)]
        awu::impl_op_assign! { impl core::ops::ShrAssign<u128>, shr_assign use core::ops::Shr<u128>, shr for $type }
        awu::impl_op_assign! { impl core::ops::ShrAssign<usize>, shr_assign use core::ops::Shr<usize>, shr for $type }

        awu::impl_op_assign! { impl core::ops::ShrAssign<i8>, shr_assign use core::ops::Shr<i8>, shr for $type }
        awu::impl_op_assign! { impl core::ops::ShrAssign<i16>, shr_assign use core::ops::Shr<i16>, shr for $type }
        awu::impl_op_assign! { impl core::ops::ShrAssign<i32>, shr_assign use core::ops::Shr<i32>, shr for $type }
        awu::impl_op_assign! { impl core::ops::ShrAssign<i64>, shr_assign use core::ops::Shr<i64>, shr for $type }
        #[cfg(has_i128)]
        awu::impl_op_assign! { impl core::ops::ShrAssign<i128>, shr_assign use core::ops::Shr<i128>, shr for $type }
        awu::impl_op_assign! { impl core::ops::ShrAssign<isize>, shr_assign use core::ops::Shr<isize>, shr for $type }

        $($($(awu::impl_from! { impl core::convert::From<$from_types>, from for $type })+)?)?
        $($($(awu::impl_try_from! { impl core::convert::TryFrom<$try_from_types>, try_from for $type where INNER: $inner_type })+)?)?
        $($($(awu::impl_into! { impl core::convert::From<$type>, from for $into_types })+)?)?
        $($($(awu::impl_try_into! { impl core::convert::TryFrom<$type where INNER: $inner_type>, try_from for $try_into_types })+)?)?

        impl core::iter::Sum for $type {
            fn sum<I: Iterator<Item=Self>>(iter: I) -> Self {
                iter.fold(Self(0), |a, b| a + b)
            }
        }
        impl<'a> core::iter::Sum<&'a Self> for $type {
            fn sum<I: Iterator<Item=&'a Self>>(iter: I) -> Self {
                iter.fold(Self(0), |a, b| a + b)
            }
        }

        impl core::iter::Product for $type {
            fn product<I: Iterator<Item=Self>>(iter: I) -> Self {
                iter.fold(Self(1), |a, b| a * b)
            }
        }
        impl<'a> core::iter::Product<&'a Self> for $type {
            fn product<I: Iterator<Item=&'a Self>>(iter: I) -> Self {
                iter.fold(Self(1), |a, b| a * b)
            }
        }

        impl core::str::FromStr for $type {
            type Err = Option<core::num::ParseIntError>;
            fn from_str(src: &str) -> Result<Self, Self::Err> {
                Self::from_str_radix(src, 10)
            }
        }

    };
}

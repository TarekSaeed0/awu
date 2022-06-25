#![no_std]

#[macro_export]
macro_rules! un_def {
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
                Self(value & Self::MAX.0)
            }

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
                Self::new(self.0 << (n % Self::BITS) | self.0 >> (Self::BITS - (n % Self::BITS)))
            }

            #[inline]
            pub const fn rotate_right(self, n: u32) -> Self {
                Self::new(self.0 >> (n % Self::BITS) | self.0 << (Self::BITS - (n % Self::BITS)))
            }

            #[inline]
            pub const fn reverse_bits(self) -> Self {
                Self::new(self.0.reverse_bits() >> (<$type>::BITS - Self::BITS))
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
                if let Some(v) = self.0.checked_div(rhs.0) {Some(Self(v))} else {None}
            }

            #[inline]
            pub const fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
                if let Some(v) = self.0.checked_div_euclid(rhs.0) {Some(Self(v))} else {None}
            }
            
            #[inline]
            pub const fn checked_rem(self, rhs: Self) -> Option<Self> {
                if let Some(v) = self.0.checked_rem(rhs.0) {Some(Self(v))} else {None}
            }

            #[inline]
            pub const fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
                if let Some(v) = self.0.checked_rem_euclid(rhs.0) {Some(Self(v))} else {None}
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
            pub const fn checked_pow(self, exp: u32) -> Option<Self> {
                match self.0.checked_pow(exp) {
                    Some(x) if x <= Self::MAX.0 => Some(Self(x)),
                    _ => None
                }
            }

            #[inline]
            pub const fn saturating_add(self, rhs: Self) -> Self {
                let v = self.0.saturating_add(rhs.0);
                if v > Self::MAX.0 {Self::MAX} else {Self(v)}
            }

            #[inline]
            pub const fn saturating_sub(self, rhs: Self) -> Self {
                Self(self.0.saturating_sub(rhs.0))
            }

            #[inline]
            pub const fn saturating_mul(self, rhs: Self) -> Self {
                let v = self.0.saturating_mul(rhs.0);
                if v > Self::MAX.0 {Self::MAX} else {Self(v)}
            }

            #[inline]
            pub const fn saturating_div(self, rhs: Self) -> Self {
                Self(self.0.saturating_div(rhs.0))
            }

            #[inline]
            pub const fn saturating_pow(self, exp: u32) -> Self {
                let v = self.0.saturating_pow(exp);
                if v > Self::MAX.0 {Self::MAX} else {Self(v)}
            }

            #[inline]
            pub const fn wrapping_add(self, rhs: Self) -> Self {
                Self::new(self.0.wrapping_add(rhs.0))
            }

            #[inline]
            pub const fn wrapping_sub(self, rhs: Self) -> Self {
                Self::new(self.0.wrapping_sub(rhs.0))
            }

            #[inline]
            pub const fn wrapping_mul(self, rhs: Self) -> Self {
                Self::new(self.0.wrapping_mul(rhs.0))
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
                Self::new(self.0.wrapping_neg())
            }

            #[inline]
            pub const fn wrapping_shl(self, rhs: u32) -> Self {
                Self::new(self.0.wrapping_shl(rhs % Self::BITS))
            }

            #[inline]
            pub const fn wrapping_shr(self, rhs: u32) -> Self {
                Self::new(self.0.wrapping_shr(rhs % Self::BITS))
            }

            #[inline]
            pub const fn wrapping_pow(self, exp: u32) -> Self {
                Self::new(self.0.wrapping_pow(exp))
            }

            #[inline]
            pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_add(rhs.0);
                (Self::new(a), b || a > Self::MAX.0)
            }

            #[inline]
            pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_sub(rhs.0);
                (Self::new(a), b)
            }

            #[inline]
            pub const fn abs_diff(self, other: Self) -> Self {
                Self(self.0.abs_diff(other.0))
            }

            #[inline]
            pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
                let (a, b) = self.0.overflowing_mul(rhs.0);
                (Self::new(a), b || a > Self::MAX.0)
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
                (Self::new(a), b)
            }

            #[inline]
            pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
                let (a, b) = self.0.overflowing_shl(rhs % Self::BITS);
                (Self::new(a), b || (rhs >= Self::BITS))
            }

            #[inline]
            pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
                let (a, b) = self.0.overflowing_shr(rhs % Self::BITS);
                (Self::new(a), b || (rhs >= Self::BITS))
            }

            #[inline]
            pub const fn overflowing_pow(self, exp: u32) -> (Self, bool) {
                let (a, b) = self.0.overflowing_pow(exp);
                (Self::new(a), b || a > Self::MAX.0)
            }

            #[inline]
            pub const fn pow(self, exp: u32) -> Self {
                let x = self.0.pow(exp);
                assert!(x <= Self::MAX.0, "attempt to multiply with overflow");
                Self::new(x)
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
                assert!(x <= Self::MAX.0, "attempt to add with overflow");
                Self::new(x)
            }

            #[inline]
            const fn checked_next_power_of_two(self) -> Option<Self> {
                match self.0.checked_next_power_of_two() {
                    Some(x) if x <= Self::MAX.0 => Some(Self(x)),
                    _ => None
                }
            }
        }
    };
}

#[cfg(test)]
mod tests {

    un_def! {
        #[allow(non_camel_case_types)] 
        struct u5(u8) where BITS: 5;
    }

    #[test]
    fn u5_consts() {
        assert_eq!(u5::MIN.0, 0);
        assert_eq!(u5::MAX.0, 31);
        assert_eq!(u5::BITS, 5);
    }

    #[test]
    fn u5_new_in_range() {
        assert_eq!(u5::new(25).0, 25);
        assert_eq!(u5::new(10).0, 10);
        assert_eq!(u5::new(31).0, 31);
        assert_eq!(u5::new(5).0, 5);
        assert_eq!(u5::new(0).0, 0);
    }

    #[test]
    fn u5_new_out_of_range() {
        assert_eq!(u5::new(32).0, 0);
        assert_eq!(u5::new(251).0, 27);
        assert_eq!(u5::new(51).0, 19);
        assert_eq!(u5::new(85).0, 21);
        assert_eq!(u5::new(255).0, 31);
    }

    #[test]
    fn u5_count_ones() {
        assert_eq!(u5::new(0b00000).count_ones(), 0);
        assert_eq!(u5::new(0b01111).count_ones(), 4);
        assert_eq!(u5::new(0b01001).count_ones(), 2);
        assert_eq!(u5::new(0b10100).count_ones(), 2);
        assert_eq!(u5::new(0b11111).count_ones(), 5);
    }
    
    #[test]
    fn u5_count_zeros() {
        assert_eq!(u5::new(0b00000).count_zeros(), 5);
        assert_eq!(u5::new(0b01010).count_zeros(), 3);
        assert_eq!(u5::new(0b00001).count_zeros(), 4);
        assert_eq!(u5::new(0b11100).count_zeros(), 2);
        assert_eq!(u5::new(0b11111).count_zeros(), 0);
    }

    #[test]
    fn u5_leading_zeros() {
        assert_eq!(u5::new(0b00000).leading_zeros(), 5);
        assert_eq!(u5::new(0b01010).leading_zeros(), 1);
        assert_eq!(u5::new(0b00011).leading_zeros(), 3);
        assert_eq!(u5::new(0b10000).leading_zeros(), 0);
        assert_eq!(u5::new(0b01101).leading_zeros(), 1);
    }

    #[test]
    fn u5_trailing_zeros() {
        assert_eq!(u5::new(0b00000).trailing_zeros(), 5);
        assert_eq!(u5::new(0b01000).trailing_zeros(), 3);
        assert_eq!(u5::new(0b10010).trailing_zeros(), 1);
        assert_eq!(u5::new(0b10000).trailing_zeros(), 4);
        assert_eq!(u5::new(0b01101).trailing_zeros(), 0);
    }

    #[test]
    fn u5_leading_ones() {
        assert_eq!(u5::new(0b00000).leading_ones(), 0);
        assert_eq!(u5::new(0b11110).leading_ones(), 4);
        assert_eq!(u5::new(0b11011).leading_ones(), 2);
        assert_eq!(u5::new(0b10100).leading_ones(), 1);
        assert_eq!(u5::new(0b11111).leading_ones(), 5);
    }

    #[test]
    fn u5_trailing_ones() {
        assert_eq!(u5::new(0b00000).trailing_ones(), 0);
        assert_eq!(u5::new(0b01111).trailing_ones(), 4);
        assert_eq!(u5::new(0b10010).trailing_ones(), 0);
        assert_eq!(u5::new(0b11111).trailing_ones(), 5);
        assert_eq!(u5::new(0b01101).trailing_ones(), 1);
    }

    #[test]
    fn u5_rotate_left() {
        assert_eq!(u5::new(0b00000).rotate_left(2), u5::new(0b00000));
        assert_eq!(u5::new(0b01111).rotate_left(3), u5::new(0b11011));
        assert_eq!(u5::new(0b10010).rotate_left(0), u5::new(0b10010));
        assert_eq!(u5::new(0b11111).rotate_left(10), u5::new(0b11111));
        assert_eq!(u5::new(0b01101).rotate_left(5), u5::new(0b01101));
    }

    #[test]
    fn u5_rotate_right() {
        assert_eq!(u5::new(0b00000).rotate_right(2), u5::new(0b00000));
        assert_eq!(u5::new(0b01101).rotate_right(3), u5::new(0b10101));
        assert_eq!(u5::new(0b10010).rotate_right(0), u5::new(0b10010));
        assert_eq!(u5::new(0b11111).rotate_right(10), u5::new(0b11111));
        assert_eq!(u5::new(0b01101).rotate_right(5), u5::new(0b01101));
    }

    #[test]
    fn u5_reverse_bits() {
        assert_eq!(u5::new(0b00000).reverse_bits(), u5::new(0b00000));
        assert_eq!(u5::new(0b01111).reverse_bits(), u5::new(0b11110));
        assert_eq!(u5::new(0b11010).reverse_bits(), u5::new(0b01011));
        assert_eq!(u5::new(0b00100).reverse_bits(), u5::new(0b00100));
        assert_eq!(u5::new(0b01101).reverse_bits(), u5::new(0b10110));
    }

    #[test]
    fn u5_checked_add() {
        assert_eq!(u5::new(10).checked_add(u5::new(13)), Some(u5::new(23)));
        assert_eq!(u5::new(31).checked_add(u5::new(1)), None);
        assert_eq!(u5::new(17).checked_add(u5::new(24)), None);
        assert_eq!(u5::new(5).checked_add(u5::new(3)), Some(u5::new(8)));
        assert_eq!(u5::new(24).checked_add(u5::new(0)), Some(u5::new(24)));
    }

    #[test]
    fn u5_checked_sub() {
        assert_eq!(u5::new(17).checked_sub(u5::new(23)), None);
        assert_eq!(u5::new(31).checked_sub(u5::new(1)), Some(u5::new(30)));
        assert_eq!(u5::new(0).checked_sub(u5::new(24)), None);
        assert_eq!(u5::new(5).checked_sub(u5::new(3)), Some(u5::new(2)));
        assert_eq!(u5::new(24).checked_sub(u5::new(0)), Some(u5::new(24)));
    }

    #[test]
    fn u5_checked_mul() {
        assert_eq!(u5::new(10).checked_mul(u5::new(13)), None);
        assert_eq!(u5::new(31).checked_mul(u5::new(1)), Some(u5::new(31)));
        assert_eq!(u5::new(17).checked_mul(u5::new(24)), None);
        assert_eq!(u5::new(6).checked_mul(u5::new(4)), Some(u5::new(24)));
        assert_eq!(u5::new(12).checked_mul(u5::new(0)), Some(u5::new(0)));
    }

    #[test]
    fn u5_checked_div() {
        assert_eq!(u5::new(23).checked_div(u5::new(10)), Some(u5::new(2)));
        assert_eq!(u5::new(9).checked_div(u5::new(1)), Some(u5::new(9)));
        assert_eq!(u5::new(0).checked_div(u5::new(24)), Some(u5::new(0)));
        assert_eq!(u5::new(5).checked_div(u5::new(3)), Some(u5::new(1)));
        assert_eq!(u5::new(24).checked_div(u5::new(0)), None);
    }

    #[test]
    fn u5_checked_div_euclid() {
        assert_eq!(u5::new(23).checked_div_euclid(u5::new(10)), Some(u5::new(2)));
        assert_eq!(u5::new(9).checked_div_euclid(u5::new(1)), Some(u5::new(9)));
        assert_eq!(u5::new(0).checked_div_euclid(u5::new(24)), Some(u5::new(0)));
        assert_eq!(u5::new(5).checked_div_euclid(u5::new(3)), Some(u5::new(1)));
        assert_eq!(u5::new(24).checked_div_euclid(u5::new(0)), None);
    }

    #[test]
    fn u5_checked_rem() {
        assert_eq!(u5::new(23).checked_rem(u5::new(10)), Some(u5::new(3)));
        assert_eq!(u5::new(9).checked_rem(u5::new(2)), Some(u5::new(1)));
        assert_eq!(u5::new(10).checked_rem(u5::new(24)), Some(u5::new(10)));
        assert_eq!(u5::new(12).checked_rem(u5::new(3)), Some(u5::new(0)));
        assert_eq!(u5::new(24).checked_rem(u5::new(0)), None);
    }

    #[test]
    fn u5_checked_rem_euclid() {
        assert_eq!(u5::new(23).checked_rem_euclid(u5::new(10)), Some(u5::new(3)));
        assert_eq!(u5::new(9).checked_rem_euclid(u5::new(2)), Some(u5::new(1)));
        assert_eq!(u5::new(10).checked_rem_euclid(u5::new(24)), Some(u5::new(10)));
        assert_eq!(u5::new(12).checked_rem_euclid(u5::new(3)), Some(u5::new(0)));
        assert_eq!(u5::new(24).checked_rem_euclid(u5::new(0)), None);
    }

    #[test]
    fn u5_checked_neg() {
        assert_eq!(u5::new(23).checked_neg(), None);
        assert_eq!(u5::new(10).checked_neg(), None);
        assert_eq!(u5::new(16).checked_neg(), None);
        assert_eq!(u5::new(0).checked_neg(), Some(u5::new(0)));
        assert_eq!(u5::new(1).checked_neg(), None);
    }
    
    #[test]
    fn u5_checked_shl() {
        assert_eq!(u5::new(0b01101).checked_shl(0), Some(u5::new(0b01101)));
        assert_eq!(u5::new(0b10101).checked_shl(1), Some(u5::new(0b01010)));
        assert_eq!(u5::new(0b00001).checked_shl(3), Some(u5::new(0b01000)));
        assert_eq!(u5::new(0b11001).checked_shl(5), None);
        assert_eq!(u5::new(0b01101).checked_shl(12), None);
    }

    #[test]
    fn u5_checked_shr() {
        assert_eq!(u5::new(0b01001).checked_shr(1), Some(u5::new(0b00100)));
        assert_eq!(u5::new(0b00111).checked_shr(0), Some(u5::new(0b00111)));
        assert_eq!(u5::new(0b00101).checked_shr(4), Some(u5::new(0b00000)));
        assert_eq!(u5::new(0b11000).checked_shr(5), None);
        assert_eq!(u5::new(0b01100).checked_shr(63), None);
    }
    
    #[test]
    fn u5_checked_pow() {
        assert_eq!(u5::new(7).checked_pow(3), None);
        assert_eq!(u5::new(23).checked_pow(0), Some(u5::new(1)));
        assert_eq!(u5::new(2).checked_pow(4), Some(u5::new(16)));
        assert_eq!(u5::new(11).checked_pow(5), None);
        assert_eq!(u5::new(1).checked_pow(63), Some(u5::new(1)));
    }

    #[test]
    fn u5_saturating_add() {
        assert_eq!(u5::new(10).saturating_add(u5::new(13)), u5::new(23));
        assert_eq!(u5::new(31).saturating_add(u5::new(1)), u5::new(31));
        assert_eq!(u5::new(17).saturating_add(u5::new(24)), u5::new(31));
        assert_eq!(u5::new(5).saturating_add(u5::new(3)), u5::new(8));
        assert_eq!(u5::new(24).saturating_add(u5::new(0)), u5::new(24));
    }

    #[test]
    fn u5_saturating_sub() {
        assert_eq!(u5::new(17).saturating_sub(u5::new(23)), u5::new(0));
        assert_eq!(u5::new(31).saturating_sub(u5::new(1)), u5::new(30));
        assert_eq!(u5::new(0).saturating_sub(u5::new(24)), u5::new(0));
        assert_eq!(u5::new(5).saturating_sub(u5::new(3)), u5::new(2));
        assert_eq!(u5::new(24).saturating_sub(u5::new(0)), u5::new(24));
    }

    #[test]
    fn u5_saturating_mul() {
        assert_eq!(u5::new(10).saturating_mul(u5::new(13)), u5::new(31));
        assert_eq!(u5::new(31).saturating_mul(u5::new(1)), u5::new(31));
        assert_eq!(u5::new(17).saturating_mul(u5::new(24)), u5::new(31));
        assert_eq!(u5::new(6).saturating_mul(u5::new(4)), u5::new(24));
        assert_eq!(u5::new(12).saturating_mul(u5::new(0)), u5::new(0));
    }

    #[test]
    fn u5_saturating_div() {
        assert_eq!(u5::new(23).saturating_div(u5::new(10)), u5::new(2));
        assert_eq!(u5::new(9).saturating_div(u5::new(1)), u5::new(9));
        assert_eq!(u5::new(0).saturating_div(u5::new(24)), u5::new(0));
        assert_eq!(u5::new(5).saturating_div(u5::new(3)), u5::new(1));
        assert_eq!(u5::new(5).saturating_div(u5::new(16)), u5::new(0));
    }
    
    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn u5_saturating_div_panic_0() {
        u5::new(17).saturating_div(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to divide by zero")]
    fn u5_saturating_div_panic_1() {
        u5::new(0).saturating_div(u5::new(0));
    }

    #[test]
    fn u5_saturating_pow() {
        assert_eq!(u5::new(7).saturating_pow(3), u5::new(31));
        assert_eq!(u5::new(23).saturating_pow(0), u5::new(1));
        assert_eq!(u5::new(2).saturating_pow(4), u5::new(16));
        assert_eq!(u5::new(11).saturating_pow(5), u5::new(31));
        assert_eq!(u5::new(1).saturating_pow(63), u5::new(1));
    }

    #[test]
    fn u5_wrapping_add() {
        assert_eq!(u5::new(10).wrapping_add(u5::new(13)), u5::new(23));
        assert_eq!(u5::new(31).wrapping_add(u5::new(1)), u5::new(0));
        assert_eq!(u5::new(17).wrapping_add(u5::new(24)), u5::new(9));
        assert_eq!(u5::new(5).wrapping_add(u5::new(3)), u5::new(8));
        assert_eq!(u5::new(24).wrapping_add(u5::new(0)), u5::new(24));
    }

    #[test]
    fn u5_wrapping_sub() {
        assert_eq!(u5::new(17).wrapping_sub(u5::new(23)), u5::new(26));
        assert_eq!(u5::new(31).wrapping_sub(u5::new(1)), u5::new(30));
        assert_eq!(u5::new(0).wrapping_sub(u5::new(24)), u5::new(8));
        assert_eq!(u5::new(5).wrapping_sub(u5::new(3)), u5::new(2));
        assert_eq!(u5::new(24).wrapping_sub(u5::new(0)), u5::new(24));
    }

    #[test]
    fn u5_wrapping_mul() {
        assert_eq!(u5::new(10).wrapping_mul(u5::new(13)), u5::new(2));
        assert_eq!(u5::new(31).wrapping_mul(u5::new(1)), u5::new(31));
        assert_eq!(u5::new(17).wrapping_mul(u5::new(24)), u5::new(24));
        assert_eq!(u5::new(6).wrapping_mul(u5::new(4)), u5::new(24));
        assert_eq!(u5::new(12).wrapping_mul(u5::new(0)), u5::new(0));
    }

    #[test]
    fn u5_wrapping_div() {
        assert_eq!(u5::new(23).wrapping_div(u5::new(10)), u5::new(2));
        assert_eq!(u5::new(9).wrapping_div(u5::new(1)), u5::new(9));
        assert_eq!(u5::new(0).wrapping_div(u5::new(24)), u5::new(0));
        assert_eq!(u5::new(5).wrapping_div(u5::new(3)), u5::new(1));
        assert_eq!(u5::new(24).wrapping_div(u5::new(5)), u5::new(4));
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn u5_wrapping_div_panic_0() {
        u5::new(25).wrapping_div(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to divide by zero")]
    fn u5_wrapping_div_panic_1() {
        u5::new(0).wrapping_div(u5::new(0));
    }

    #[test]
    fn u5_wrapping_div_euclid() {
        assert_eq!(u5::new(23).wrapping_div_euclid(u5::new(10)), u5::new(2));
        assert_eq!(u5::new(9).wrapping_div_euclid(u5::new(1)), u5::new(9));
        assert_eq!(u5::new(0).wrapping_div_euclid(u5::new(24)), u5::new(0));
        assert_eq!(u5::new(5).wrapping_div_euclid(u5::new(3)), u5::new(1));
        assert_eq!(u5::new(24).wrapping_div_euclid(u5::new(5)), u5::new(4));
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn u5_wrapping_div_euclid_panic_0() {
        u5::new(5).wrapping_div_euclid(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to divide by zero")]
    fn u5_wrapping_div_euclid_panic_1() {
        u5::new(0).wrapping_div_euclid(u5::new(0));
    }

    #[test]
    fn u5_wrapping_rem() {
        assert_eq!(u5::new(23).wrapping_rem(u5::new(10)), u5::new(3));
        assert_eq!(u5::new(9).wrapping_rem(u5::new(2)), u5::new(1));
        assert_eq!(u5::new(10).wrapping_rem(u5::new(24)), u5::new(10));
        assert_eq!(u5::new(12).wrapping_rem(u5::new(3)), u5::new(0));
        assert_eq!(u5::new(24).wrapping_rem(u5::new(12)), u5::new(0));
    }

    #[test]
    #[should_panic(expected = "attempt to calculate the remainder with a divisor of zero")]
    fn u5_wrapping_rem_panic_0() {
        u5::new(31).wrapping_rem(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to calculate the remainder with a divisor of zero")]
    fn u5_wrapping_rem_panic_1() {
        u5::new(0).wrapping_rem(u5::new(0));
    }

    #[test]
    fn u5_wrapping_rem_euclid() {
        assert_eq!(u5::new(23).wrapping_rem_euclid(u5::new(10)), u5::new(3));
        assert_eq!(u5::new(9).wrapping_rem_euclid(u5::new(2)), u5::new(1));
        assert_eq!(u5::new(10).wrapping_rem_euclid(u5::new(24)), u5::new(10));
        assert_eq!(u5::new(12).wrapping_rem_euclid(u5::new(3)), u5::new(0));
        assert_eq!(u5::new(24).wrapping_rem_euclid(u5::new(12)), u5::new(0));
    }

    #[test]
    #[should_panic(expected = "attempt to calculate the remainder with a divisor of zero")]
    fn u5_wrapping_rem_euclid_panic_0() {
        u5::new(20).wrapping_rem_euclid(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to calculate the remainder with a divisor of zero")]
    fn u5_wrapping_rem_euclid_panic_1() {
        u5::new(0).wrapping_rem_euclid(u5::new(0));
    }

    #[test]
    fn u5_wrapping_neg() {
        assert_eq!(u5::new(23).wrapping_neg(), u5::new(9));
        assert_eq!(u5::new(10).wrapping_neg(), u5::new(22));
        assert_eq!(u5::new(16).wrapping_neg(), u5::new(16));
        assert_eq!(u5::new(0).wrapping_neg(), u5::new(0));
        assert_eq!(u5::new(1).wrapping_neg(), u5::new(31));
    }
    
    #[test]
    fn u5_wrapping_shl() {
        assert_eq!(u5::new(0b01101).wrapping_shl(0), u5::new(0b01101));
        assert_eq!(u5::new(0b10101).wrapping_shl(1), u5::new(0b01010));
        assert_eq!(u5::new(0b00001).wrapping_shl(3), u5::new(0b01000));
        assert_eq!(u5::new(0b11001).wrapping_shl(5), u5::new(0b11001));
        assert_eq!(u5::new(0b01101).wrapping_shl(12), u5::new(0b10100));
    }

    #[test]
    fn u5_wrapping_shr() {
        assert_eq!(u5::new(0b01001).wrapping_shr(1), u5::new(0b00100));
        assert_eq!(u5::new(0b00111).wrapping_shr(0), u5::new(0b00111));
        assert_eq!(u5::new(0b00101).wrapping_shr(4), u5::new(0b00000));
        assert_eq!(u5::new(0b11000).wrapping_shr(5), u5::new(0b11000));
        assert_eq!(u5::new(0b01100).wrapping_shr(63), u5::new(0b00001));
    }
    
    #[test]
    fn u5_wrapping_pow() {
        assert_eq!(u5::new(7).wrapping_pow(3), u5::new(23));
        assert_eq!(u5::new(23).wrapping_pow(0), u5::new(1));
        assert_eq!(u5::new(2).wrapping_pow(4), u5::new(16));
        assert_eq!(u5::new(11).wrapping_pow(5), u5::new(27));
        assert_eq!(u5::new(1).wrapping_pow(63), u5::new(1));
    }

    
    #[test]
    fn u5_overflowing_add() {
        assert_eq!(u5::new(10).overflowing_add(u5::new(13)), (u5::new(23), false));
        assert_eq!(u5::new(31).overflowing_add(u5::new(1)), (u5::new(0), true));
        assert_eq!(u5::new(17).overflowing_add(u5::new(24)), (u5::new(9), true));
        assert_eq!(u5::new(5).overflowing_add(u5::new(3)), (u5::new(8), false));
        assert_eq!(u5::new(24).overflowing_add(u5::new(0)), (u5::new(24), false));
    }

    #[test]
    fn u5_overflowing_sub() {
        assert_eq!(u5::new(17).overflowing_sub(u5::new(23)), (u5::new(26), true));
        assert_eq!(u5::new(31).overflowing_sub(u5::new(1)), (u5::new(30), false));
        assert_eq!(u5::new(0).overflowing_sub(u5::new(24)), (u5::new(8), true));
        assert_eq!(u5::new(5).overflowing_sub(u5::new(3)), (u5::new(2), false));
        assert_eq!(u5::new(24).overflowing_sub(u5::new(0)), (u5::new(24), false));
    }

    #[test]
    fn u5_abs_diff() {
        assert_eq!(u5::new(17).abs_diff(u5::new(23)), u5::new(6));
        assert_eq!(u5::new(31).abs_diff(u5::new(1)), u5::new(30));
        assert_eq!(u5::new(0).abs_diff(u5::new(24)), u5::new(24));
        assert_eq!(u5::new(5).abs_diff(u5::new(3)), u5::new(2));
        assert_eq!(u5::new(24).abs_diff(u5::new(0)), u5::new(24));
    }

    #[test]
    fn u5_overflowing_mul() {
        assert_eq!(u5::new(10).overflowing_mul(u5::new(13)), (u5::new(2), true));
        assert_eq!(u5::new(31).overflowing_mul(u5::new(1)), (u5::new(31), false));
        assert_eq!(u5::new(17).overflowing_mul(u5::new(24)), (u5::new(24), true));
        assert_eq!(u5::new(6).overflowing_mul(u5::new(4)), (u5::new(24), false));
        assert_eq!(u5::new(12).overflowing_mul(u5::new(0)), (u5::new(0), false));
    }

    #[test]
    fn u5_overflowing_div() {
        assert_eq!(u5::new(23).overflowing_div(u5::new(10)), (u5::new(2), false));
        assert_eq!(u5::new(9).overflowing_div(u5::new(1)), (u5::new(9), false));
        assert_eq!(u5::new(0).overflowing_div(u5::new(24)), (u5::new(0), false));
        assert_eq!(u5::new(5).overflowing_div(u5::new(3)), (u5::new(1), false));
        assert_eq!(u5::new(24).overflowing_div(u5::new(5)), (u5::new(4), false));
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn u5_overflowing_div_panic_0() {
        u5::new(25).overflowing_div(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to divide by zero")]
    fn u5_overflowing_div_panic_1() {
        u5::new(0).overflowing_div(u5::new(0));
    }

    #[test]
    fn u5_overflowing_div_euclid() {
        assert_eq!(u5::new(23).overflowing_div_euclid(u5::new(10)), (u5::new(2), false));
        assert_eq!(u5::new(9).overflowing_div_euclid(u5::new(1)), (u5::new(9), false));
        assert_eq!(u5::new(0).overflowing_div_euclid(u5::new(24)), (u5::new(0), false));
        assert_eq!(u5::new(5).overflowing_div_euclid(u5::new(3)), (u5::new(1), false));
        assert_eq!(u5::new(24).overflowing_div_euclid(u5::new(5)), (u5::new(4), false));
    }

    #[test]
    #[should_panic(expected = "attempt to divide by zero")]
    fn u5_overflowing_div_euclid_panic_0() {
        u5::new(5).overflowing_div_euclid(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to divide by zero")]
    fn u5_overflowing_div_euclid_panic_1() {
        u5::new(0).overflowing_div_euclid(u5::new(0));
    }

    #[test]
    fn u5_overflowing_rem() {
        assert_eq!(u5::new(23).overflowing_rem(u5::new(10)), (u5::new(3), false));
        assert_eq!(u5::new(9).overflowing_rem(u5::new(2)), (u5::new(1), false));
        assert_eq!(u5::new(10).overflowing_rem(u5::new(24)), (u5::new(10), false));
        assert_eq!(u5::new(12).overflowing_rem(u5::new(3)), (u5::new(0), false));
        assert_eq!(u5::new(24).overflowing_rem(u5::new(12)), (u5::new(0), false));
    }

    #[test]
    #[should_panic(expected = "attempt to calculate the remainder with a divisor of zero")]
    fn u5_overflowing_rem_panic_0() {
        u5::new(31).overflowing_rem(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to calculate the remainder with a divisor of zero")]
    fn u5_overflowing_rem_panic_1() {
        u5::new(0).overflowing_rem(u5::new(0));
    }

    #[test]
    fn u5_overflowing_rem_euclid() {
        assert_eq!(u5::new(23).overflowing_rem_euclid(u5::new(10)), (u5::new(3), false));
        assert_eq!(u5::new(9).overflowing_rem_euclid(u5::new(2)), (u5::new(1), false));
        assert_eq!(u5::new(10).overflowing_rem_euclid(u5::new(24)), (u5::new(10), false));
        assert_eq!(u5::new(12).overflowing_rem_euclid(u5::new(3)), (u5::new(0), false));
        assert_eq!(u5::new(24).overflowing_rem_euclid(u5::new(12)), (u5::new(0), false));
    }

    #[test]
    #[should_panic(expected = "attempt to calculate the remainder with a divisor of zero")]
    fn u5_overflowing_rem_euclid_panic_0() {
        u5::new(20).overflowing_rem_euclid(u5::new(0));
    }

    #[test]
    #[should_panic(expected =  "attempt to calculate the remainder with a divisor of zero")]
    fn u5_overflowing_rem_euclid_panic_1() {
        u5::new(0).overflowing_rem_euclid(u5::new(0));
    }

    #[test]
    fn u5_overflowing_neg() {
        assert_eq!(u5::new(23).overflowing_neg(), (u5::new(9), true));
        assert_eq!(u5::new(10).overflowing_neg(), (u5::new(22), true));
        assert_eq!(u5::new(16).overflowing_neg(), (u5::new(16), true));
        assert_eq!(u5::new(0).overflowing_neg(), (u5::new(0), false));
        assert_eq!(u5::new(1).overflowing_neg(), (u5::new(31), true));
    }
    
    #[test]
    fn u5_overflowing_shl() {
        assert_eq!(u5::new(0b01101).overflowing_shl(0), (u5::new(0b01101), false));
        assert_eq!(u5::new(0b10101).overflowing_shl(1), (u5::new(0b01010), false));
        assert_eq!(u5::new(0b00001).overflowing_shl(3), (u5::new(0b01000), false));
        assert_eq!(u5::new(0b11001).overflowing_shl(5), (u5::new(0b11001), true));
        assert_eq!(u5::new(0b01101).overflowing_shl(12), (u5::new(0b10100), true));
    }

    #[test]
    fn u5_overflowing_shr() {
        assert_eq!(u5::new(0b01001).overflowing_shr(1), (u5::new(0b00100), false));
        assert_eq!(u5::new(0b00111).overflowing_shr(0), (u5::new(0b00111), false));
        assert_eq!(u5::new(0b00101).overflowing_shr(4), (u5::new(0b00000), false));
        assert_eq!(u5::new(0b11000).overflowing_shr(5), (u5::new(0b11000), true));
        assert_eq!(u5::new(0b01100).overflowing_shr(63), (u5::new(0b00001), true));
    }
    
    #[test]
    fn u5_overflowing_pow() {
        assert_eq!(u5::new(7).overflowing_pow(3), (u5::new(23), true));
        assert_eq!(u5::new(23).overflowing_pow(0), (u5::new(1), false));
        assert_eq!(u5::new(2).overflowing_pow(4), (u5::new(16), false));
        assert_eq!(u5::new(11).overflowing_pow(5), (u5::new(27), true));
        assert_eq!(u5::new(1).overflowing_pow(63), (u5::new(1), false));
    }
}
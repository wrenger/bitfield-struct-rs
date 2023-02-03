pub use bitfield_struct_derive::bitfield;

/// The heart of the bitfield macro.
/// It copies bits (with different offsets) from `src` to `dst`.
///
/// This function is used both for the getters and setters of the bitfield struct.
///
///  General idea:
/// - Copy prefix bits
/// - Copy aligned u8
/// - Copy suffix bits
///
/// Possible future optimization:
/// - Copy and shift with larger instructions (u16/u32/u64) if the buffers are large enough
///
/// FIXME: Use mutable reference as soon as `const_mut_refs` is stable
#[inline(always)]
pub fn bit_copy(dst: &mut [u8], dst_off: usize, src: &[u8], src_off: usize, len: usize) {
    debug_assert!(len > 0);
    debug_assert!(dst.len() * 8 >= dst_off + len);
    debug_assert!(src.len() * 8 >= src_off + len);

    // normalize input
    let dst = &mut dst[dst_off / 8..];
    let src = &src[src_off / 8..];
    let dst_off = dst_off % 8;
    let src_off = src_off % 8;

    if len < (8 - dst_off) {
        // edge case if there are less then one byte to be copied
        single_byte(&mut dst[0], dst_off, src, src_off, len);
    } else if dst_off == src_off {
        copy_aligned(dst, src, dst_off, len);
    } else {
        copy_unaligned(dst, dst_off, src, src_off, len);
    }
}

#[inline(always)]
fn single_byte(dst: &mut u8, dst_off: usize, src: &[u8], src_off: usize, len: usize) {
    let mask = (u8::MAX >> (8 - len)) << dst_off;
    *dst &= !mask;
    *dst |= ((src[0] >> src_off) << dst_off) & mask;

    // exceeding a single byte of the src buffer
    if len + src_off > 8 {
        *dst |= (src[1] << (8 - src_off + dst_off)) & mask;
    }
}

#[inline(always)]
fn copy_unaligned(
    mut dst: &mut [u8],
    dst_off: usize,
    mut src: &[u8],
    mut src_off: usize,
    mut len: usize,
) {
    debug_assert!(0 < dst_off && dst_off < 8 && 0 < src_off && src_off < 8);
    debug_assert!(dst.len() * 8 >= dst_off + len);
    debug_assert!(src.len() * 8 >= src_off + len);

    // copy dst prefix -> byte-align dst
    if dst_off > 0 {
        let prefix = 8 - dst_off;
        let mask = u8::MAX << dst_off;
        dst[0] &= !mask;
        dst[0] |= (src[0] >> src_off) << dst_off;

        // exceeding a single byte of the src buffer
        src_off += prefix;
        if let Some(reminder) = src_off.checked_sub(8) {
            src = &src[1..];
            if reminder > 0 {
                dst[0] |= src[0] << (dst_off + reminder)
            }
            src_off = reminder
        }
        dst = &mut dst[1..];
        len -= prefix;
    }

    // copy middle
    for i in 0..len / 8 {
        dst[i] = (src[i] >> src_off) | (src[i + 1] << (8 - src_off));
    }

    // suffix
    let suffix = len % 8;
    if suffix > 0 {
        let last = len / 8;
        let mask = u8::MAX >> (8 - suffix);
        dst[last] &= !mask;
        dst[last] |= src[last] >> src_off;

        // exceeding a single byte of the src buffer
        if suffix + src_off > 8 {
            dst[last] |= (src[last + 1] << (8 - src_off)) & mask;
        }
    }
}
#[inline(always)]
fn copy_aligned(mut dst: &mut [u8], mut src: &[u8], off: usize, mut len: usize) {
    debug_assert!(0 < off && off < 8);
    debug_assert!(dst.len() * 8 >= off + len);
    debug_assert!(src.len() * 8 >= off + len);

    // copy prefix -> byte-align dst
    if off > 0 {
        let prefix = 8 - off;
        let mask = u8::MAX << off;
        dst[0] &= !mask;
        dst[0] |= src[0] & mask;

        src = &src[1..];
        dst = &mut dst[1..];
        len -= prefix;
    }

    // copy middle
    let bytes = len / 8;
    dst[..bytes].copy_from_slice(&src[..bytes]);

    // copy suffix
    let suffix = len % 8;
    if suffix > 0 {
        let last = len / 8;
        let mask = u8::MAX >> (8 - suffix);
        dst[last] &= !mask;
        dst[last] |= src[last];
    }
}

#[cfg(test)]
mod test {
    use std::fmt;

    use super::bitfield;

    #[test]
    fn copy_bits_single_bit() {
        // single byte
        let src = &[0b00100000];
        let dst = &mut [0b10111111];
        super::bit_copy(dst, 6, src, 5, 1);
        assert_eq!(dst, &[0b11111111]);
        // reversed
        let src = &[!0b00100000];
        let dst = &mut [!0b10111111];
        super::bit_copy(dst, 6, src, 5, 1);
        assert_eq!(dst, &[!0b11111111]);
    }

    #[test]
    fn copy_bits_single_byte() {
        // single byte
        let src = &[0b00111000];
        let dst = &mut [0b10001111];
        super::bit_copy(dst, 4, src, 3, 3);
        assert_eq!(dst, &[0b11111111]);
        // reversed
        let src = &[!0b00111000];
        let dst = &mut [!0b10001111];
        super::bit_copy(dst, 4, src, 3, 3);
        assert_eq!(dst, &[!0b11111111]);
    }

    #[test]
    fn copy_bits_unaligned() {
        // two to single byte
        let src = &[0b00000000, 0b11000000, 0b00000111, 0b00000000];
        let dst = &mut [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        super::bit_copy(dst, 17, src, 14, 5);
        assert_eq!(dst, &[0b00000000, 0b00000000, 0b00111110, 0b0000000]);
        // reversed
        let src = &[!0b00000000, !0b11000000, !0b00000111, !0b00000000];
        let dst = &mut [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        super::bit_copy(dst, 17, src, 14, 5);
        assert_eq!(dst, &[!0b00000000, !0b00000000, !0b00111110, !0b0000000]);

        // over two bytes
        let src = &[0b00000000, 0b11000000, 0b00000111, 0b00000000];
        let dst = &mut [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        super::bit_copy(dst, 23, src, 14, 5);
        assert_eq!(dst, &[0b00000000, 0b00000000, 0b10000000, 0b00001111]);
        // reversed
        let src = &[!0b00000000, !0b11000000, !0b00000111, !0b00000000];
        let dst = &mut [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        super::bit_copy(dst, 23, src, 14, 5);
        assert_eq!(dst, &[!0b00000000, !0b00000000, !0b10000000, !0b00001111]);

        // over three bytes
        let src = &[0b11000000, 0b11111111, 0b00000111, 0b00000000];
        let dst = &mut [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        super::bit_copy(dst, 15, src, 6, 13);
        assert_eq!(dst, &[0b00000000, 0b10000000, 0b11111111, 0b00001111]);
        // reversed
        let src = &[!0b11000000, !0b11111111, !0b00000111, !0b00000000];
        let dst = &mut [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        super::bit_copy(dst, 15, src, 6, 13);
        assert_eq!(dst, &[!0b00000000, !0b10000000, !0b11111111, !0b00001111]);
    }

    #[test]
    fn copy_bits_aligned() {
        // over two bytes
        let src = &[0b00000000, 0b11000000, 0b00000111, 0b00000000];
        let dst = &mut [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        super::bit_copy(dst, 14, src, 14, 5);
        assert_eq!(dst, src);
        // reversed
        let src = &[!0b00000000, !0b11000000, !0b00000111, !0b00000000];
        let dst = &mut [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        super::bit_copy(dst, 14, src, 14, 5);
        assert_eq!(dst, src);

        // over three bytes
        let src = &[0b11000000, 0b11100111, 0b00000111, 0b00000000];
        let dst = &mut [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        super::bit_copy(dst, 14, src, 6, 13);
        assert_eq!(dst, &[0b00000000, 0b11000000, 0b11100111, 0b00000111]);
        // reversed
        let src = &[!0b11000000, !0b11100111, !0b00000111, !0b00000000];
        let dst = &mut [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        super::bit_copy(dst, 14, src, 6, 13);
        assert_eq!(dst, &[!0b00000000, !0b11000000, !0b11100111, !0b00000111]);
    }

    #[test]
    fn members() {
        /// A test bitfield with documentation
        #[bitfield(u64)]
        struct MyBitfield {
            /// defaults to 16 bits for u16
            int: u16,
            /// interpreted as 1 bit flag
            flag: bool,
            /// custom bit size
            #[bits(1)]
            tiny: u8,
            /// sign extend for signed integers
            #[bits(13)]
            negative: i16,
            /// supports any type that implements `From<u64>` and `Into<u64>`
            #[bits(16)]
            custom: CustomEnum,
            /// public field -> public accessor functions
            #[bits(12)]
            pub public: usize,
            /// padding
            #[bits(5)]
            _p: u8,
            /// zero-sized members are ignored
            #[bits(0)]
            _completely_ignored: String,
        }

        /// A custom enum
        #[derive(Debug, PartialEq, Eq)]
        #[repr(u64)]
        enum CustomEnum {
            A = 0,
            B = 1,
            C = 2,
        }
        impl From<u64> for CustomEnum {
            fn from(value: u64) -> Self {
                match value {
                    0 => Self::A,
                    1 => Self::B,
                    _ => Self::C,
                }
            }
        }
        impl From<CustomEnum> for u64 {
            fn from(value: CustomEnum) -> Self {
                value as _
            }
        }

        let mut val = MyBitfield::new()
            .with_int(3 << 15)
            .with_flag(true)
            .with_tiny(1)
            .with_negative(-3)
            .with_custom(CustomEnum::B)
            .with_public(2);

        println!("{val:?}");

        let raw: u64 = val.into();
        println!("{raw:b}");

        assert_eq!(val.int(), 3 << 15);
        assert_eq!(val.flag(), true);
        assert_eq!(val.negative(), -3);
        assert_eq!(val.tiny(), 1);
        assert_eq!(val.custom(), CustomEnum::B);
        assert_eq!(val.public(), 2);

        // const members
        assert_eq!(MyBitfield::FLAG_BITS, 1);
        assert_eq!(MyBitfield::FLAG_OFFSET, 16);

        val.set_negative(1);
        assert_eq!(val.negative(), 1);

        let pte = val.with_flag(false);
        assert_eq!(pte.flag(), false);
    }

    #[test]
    fn attrs() {
        /// We have a custom debug implementation -> opt out
        #[bitfield(u64)]
        #[derive(PartialEq, Eq, Default)]
        struct Full {
            data: u64,
        }

        let full = Full::default();
        assert_eq!(u64::from(full), u64::from(Full::new()));

        let full = Full::new().with_data(u64::MAX);
        assert_eq!(full.data(), u64::MAX);
        assert!(full == Full::new().with_data(u64::MAX));
    }

    #[test]
    fn debug() {
        /// We have a custom debug implementation -> opt out
        #[bitfield(u64, debug = false)]
        struct Full {
            data: u64,
        }

        impl fmt::Debug for Full {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "0x{:x}", self.data())
            }
        }

        let full = Full::new().with_data(123);
        println!("{full:?}");
    }
}

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
pub const fn bit_copy<const D: usize>(
    mut dst: [u8; D],
    dst_off: usize,
    src: &[u8],
    src_off: usize,
    len: usize,
) -> [u8; D] {
    debug_assert!(len > 0);
    debug_assert!(dst.len() * 8 >= dst_off + len);
    debug_assert!(src.len() * 8 >= src_off + len);

    if len == 1 {
        let dst_i = dst_off / 8;
        dst[dst_i] = single_bit(dst[dst_i], dst_off % 8, src, src_off);
        dst
    } else if len < (8 - (dst_off % 8)) {
        // edge case if there are less then one byte to be copied
        let dst_i = dst_off / 8;
        dst[dst_i] = single_byte(dst[dst_i], dst_off % 8, src, src_off, len);
        dst
    } else if dst_off % 8 == src_off % 8 {
        copy_aligned(dst, dst_off / 8, src, src_off / 8, dst_off % 8, len)
    } else {
        copy_unaligned(dst, dst_off, src, src_off, len)
    }
}

#[inline(always)]
pub const fn is_bit_set(src: &[u8], i: usize) -> bool {
    debug_assert!(i < src.len() * 8);
    (src[i / 8] >> (i % 8)) & 1 != 0
}

#[inline(always)]
const fn single_bit(dst: u8, dst_off: usize, src: &[u8], src_off: usize) -> u8 {
    debug_assert!(dst_off < 8);
    if is_bit_set(src, src_off) {
        dst | (1 << dst_off)
    } else {
        dst & !(1 << dst_off)
    }
}

#[inline(always)]
const fn single_byte(dst: u8, dst_off: usize, src: &[u8], src_off: usize, len: usize) -> u8 {
    debug_assert!(dst_off < 8);

    let src_i = src_off / 8;
    let src_off = src_off % 8;

    let mask = (u8::MAX >> (8 - len)) << dst_off;
    let mut dst = dst & !mask;
    dst |= ((src[src_i] >> src_off) << dst_off) & mask;

    // exceeding a single byte of the src buffer
    if len + src_off > 8 {
        dst |= (src[src_i + 1] << (8 - src_off + dst_off)) & mask;
    }
    dst
}

#[inline(always)]
const fn copy_unaligned<const D: usize>(
    mut dst: [u8; D],
    mut dst_off: usize,
    src: &[u8],
    mut src_off: usize,
    mut len: usize,
) -> [u8; D] {
    debug_assert!(src_off % 8 != 0 || dst_off % 8 != 0);
    debug_assert!(dst.len() * 8 >= dst_off + len);
    debug_assert!(src.len() * 8 >= src_off + len);

    let mut dst_i = dst_off / 8;
    dst_off %= 8;
    let mut src_i = src_off / 8;
    src_off %= 8;

    // copy dst prefix -> byte-align dst
    if dst_off > 0 {
        let prefix = 8 - dst_off;
        let mask = u8::MAX << dst_off;
        dst[dst_i] &= !mask;
        dst[dst_i] |= (src[src_i] >> src_off) << dst_off;

        // exceeding a single byte of the src buffer
        dst_off += 8 - src_off;
        src_off += prefix;
        if let Some(reminder) = src_off.checked_sub(8) {
            src_i += 1;
            if reminder > 0 {
                dst[dst_i] |= src[src_i] << dst_off
            }
            src_off = reminder
        }
        dst_i += 1;
        len -= prefix;
    }

    // copy middle
    let mut i = 0;
    while i < len / 8 {
        dst[dst_i + i] = (src[src_i + i] >> src_off) | (src[src_i + i + 1] << (8 - src_off));
        i += 1;
    }

    // suffix
    let suffix = len % 8;
    if suffix > 0 {
        let last = len / 8;
        let mask = u8::MAX >> (8 - suffix);
        dst[dst_i + last] &= !mask;
        dst[dst_i + last] |= src[src_i + last] >> src_off;

        // exceeding a single byte of the src buffer
        if suffix + src_off > 8 {
            dst[dst_i + last] |= (src[src_i + last + 1] << (8 - src_off)) & mask;
        }
    }
    dst
}
#[inline(always)]
const fn copy_aligned<const D: usize>(
    mut dst: [u8; D],
    mut dst_i: usize,
    src: &[u8],
    mut src_i: usize,
    off: usize,
    mut len: usize,
) -> [u8; D] {
    debug_assert!(off < 8);
    debug_assert!(dst.len() * 8 >= dst_i * 8 + len);
    debug_assert!(src.len() * 8 >= src_i * 8 + len);

    // copy prefix -> byte-align dst
    if off > 0 {
        let prefix = 8 - (off % 8);
        let mask = u8::MAX << (off % 8);
        dst[dst_i] &= !mask;
        dst[dst_i] |= src[src_i] & mask;

        src_i += 1;
        dst_i += 1;
        len -= prefix;
    }

    // copy middle
    let mut i = 0;
    while i < len / 8 {
        dst[dst_i + i] = src[src_i + i];
        i += 1;
    }

    // copy suffix
    let suffix = len % 8;
    if suffix > 0 {
        let last = len / 8;
        let mask = u8::MAX >> (8 - suffix);
        dst[dst_i + last] &= !mask;
        dst[dst_i + last] |= src[src_i + last];
    }
    dst
}

#[cfg(test)]
mod test {

    #[allow(unused)]
    fn b_print(b: &[u8]) {
        for v in b.iter().rev() {
            print!("{v:08b} ");
        }
        println!()
    }

    #[test]
    fn copy_bits_single_bit() {
        // single byte
        let src = [0b00100000];
        let dst = [0b10111111];
        let dst = super::bit_copy(dst, 6, &src, 5, 1);
        assert_eq!(dst, [0b11111111]);
        // reversed
        let src = [!0b00100000];
        let dst = [!0b10111111];
        let dst = super::bit_copy(dst, 6, &src, 5, 1);
        assert_eq!(dst, [!0b11111111]);
    }

    #[test]
    fn copy_bits_single_byte() {
        // single byte
        let src = [0b00111000];
        let dst = [0b10001111];
        let dst = super::bit_copy(dst, 4, &src, 3, 3);
        assert_eq!(dst, [0b11111111]);
        // reversed
        let src = [!0b00111000];
        let dst = [!0b10001111];
        let dst = super::bit_copy(dst, 4, &src, 3, 3);
        assert_eq!(dst, [!0b11111111]);
    }

    #[test]
    fn copy_bits_unaligned() {
        // two to single byte
        let src = [0b00000000, 0b11000000, 0b00000111, 0b00000000];
        let dst = [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        let dst = super::bit_copy(dst, 17, &src, 14, 5);
        assert_eq!(dst, [0b00000000, 0b00000000, 0b00111110, 0b0000000]);
        // reversed
        let src = [!0b00000000, !0b11000000, !0b00000111, !0b00000000];
        let dst = [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        let dst = super::bit_copy(dst, 17, &src, 14, 5);
        assert_eq!(dst, [!0b00000000, !0b00000000, !0b00111110, !0b0000000]);

        // over two bytes
        let src = [0b00000000, 0b11000000, 0b00000111, 0b00000000];
        let dst = [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        let dst = super::bit_copy(dst, 23, &src, 14, 5);
        assert_eq!(dst, [0b00000000, 0b00000000, 0b10000000, 0b00001111]);
        // reversed
        let src = [!0b00000000, !0b11000000, !0b00000111, !0b00000000];
        let dst = [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        let dst = super::bit_copy(dst, 23, &src, 14, 5);
        assert_eq!(dst, [!0b00000000, !0b00000000, !0b10000000, !0b00001111]);

        // over three bytes
        let src = [0b11000000, 0b11111111, 0b00000111, 0b00000000];
        let dst = [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        let dst = super::bit_copy(dst, 15, &src, 6, 13);
        assert_eq!(dst, [0b00000000, 0b10000000, 0b11111111, 0b00001111]);
        // reversed
        let src = [!0b11000000, !0b11111111, !0b00000111, !0b00000000];
        let dst = [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        let dst = super::bit_copy(dst, 15, &src, 6, 13);
        assert_eq!(dst, [!0b00000000, !0b10000000, !0b11111111, !0b00001111]);

        // prefix exceeds a single byte
        let src = [0b00000000, 0b10000000, 0b11111111, 0b00000111];
        let dst = [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        let dst = super::bit_copy(dst, 20, &src, 15, 12);
        assert_eq!(dst, [0b00000000, 0b00000000, 0b11110000, 0b11111111]);
        // reversed
        let src = [!0b00000000, !0b10000000, !0b11111111, !0b00000111];
        let dst = [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        let dst = super::bit_copy(dst, 20, &src, 15, 12);
        assert_eq!(dst, [!0b00000000, !0b00000000, !0b11110000, !0b11111111]);
    }

    #[test]
    fn copy_bits_aligned() {
        // over two bytes
        let src = [0b00000000, 0b11000000, 0b00000111, 0b00000000];
        let dst = [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        let dst = super::bit_copy(dst, 14, &src, 14, 5);
        assert_eq!(dst, src);
        // reversed
        let src = [!0b00000000, !0b11000000, !0b00000111, !0b00000000];
        let dst = [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        let dst = super::bit_copy(dst, 14, &src, 14, 5);
        assert_eq!(dst, src);

        // over three bytes
        let src = [0b11000000, 0b11100111, 0b00000111, 0b00000000];
        let dst = [0b00000000, 0b00000000, 0b00000000, 0b00000000];
        let dst = super::bit_copy(dst, 14, &src, 6, 13);
        assert_eq!(dst, [0b00000000, 0b11000000, 0b11100111, 0b00000111]);
        // reversed
        let src = [!0b11000000, !0b11100111, !0b00000111, !0b00000000];
        let dst = [!0b00000000, !0b00000000, !0b00000000, !0b00000000];
        let dst = super::bit_copy(dst, 14, &src, 6, 13);
        assert_eq!(dst, [!0b00000000, !0b11000000, !0b11100111, !0b00000111]);

        // all bits
        let src = [0xff, 0xff, 0xff, 0xff];
        let dst = [0, 0, 0, 0];
        let dst = super::bit_copy(dst, 0, &src, 0, 4 * 8);
        assert_eq!(dst, [0xff, 0xff, 0xff, 0xff]);
        // reversed
        let src = [0, 0, 0, 0];
        let dst = [0xff, 0xff, 0xff, 0xff];
        let dst = super::bit_copy(dst, 0, &src, 0, 4 * 8);
        assert_eq!(dst, [0, 0, 0, 0]);
    }
}

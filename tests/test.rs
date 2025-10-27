use std::fmt;

use bitfield_struct::{bitenum, bitfield};

#[test]
fn members() {
    /// A test bitfield with documentation
    #[bitfield(u64, hash = true)]
    #[derive(PartialEq, Eq)] // <- Attributes after `bitfield` are carried over
    struct MyBitfield {
        /// Defaults to 16 bits for u16
        int: u16,
        /// Interpreted as 1 bit flag, with a custom default value
        #[bits(default = true)]
        flag: bool,
        /// Custom bit size
        #[bits(1)]
        tiny: u8,
        /// Sign extend for signed integers
        #[bits(13)]
        negative: i16,
        /// Supports any type with `into_bits`/`from_bits` functions
        #[bits(16)]
        custom: CustomEnum,
        /// Public field -> public accessor functions
        #[bits(10)]
        pub public: usize,
        /// Also supports read-only fields
        #[bits(1, access = RO)]
        read_only: bool,
        /// And write-only fields
        #[bits(1, access = WO)]
        write_only: bool,
        /// Padding
        #[bits(5)]
        __: u8,
    }

    /// A custom enum
    #[derive(Debug, PartialEq, Eq, Hash)]
    #[repr(u64)]
    enum CustomEnum {
        A = 0,
        B = 1,
        C = 2,
    }
    impl CustomEnum {
        const fn into_bits(self) -> u64 {
            self as _
        }
        const fn from_bits(value: u64) -> Self {
            match value {
                0 => Self::A,
                1 => Self::B,
                _ => Self::C,
            }
        }
    }

    let mut val = MyBitfield::new()
        .with_int(3 << 15)
        .with_tiny(1)
        .with_negative(-3)
        .with_public(2)
        // Would not compile
        // .with_read_only(true)
        .with_write_only(false);

    println!("{val:?}");

    let raw: u64 = val.into();
    println!("{raw:b}");

    assert_eq!(val.custom(), CustomEnum::A);
    val.set_custom(CustomEnum::B);

    assert_eq!(val.int(), 3 << 15);
    assert_eq!(val.flag(), true); // from default
    assert_eq!(val.negative(), -3);
    assert_eq!(val.tiny(), 1);
    assert_eq!(val.custom(), CustomEnum::B);
    assert_eq!(val.public(), 2);
    assert_eq!(val.read_only(), false);

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
    /// We have a custom default
    #[bitfield(u64, default = false)]
    #[derive(PartialEq, Eq)]
    struct Full {
        data: u64,
    }
    impl Default for Full {
        fn default() -> Self {
            Self(0)
        }
    }

    let full = Full::default();
    assert_eq!(u64::from(full), u64::from(Full::new()));

    let full = Full::new().with_data(u64::MAX);
    assert_eq!(full.data(), u64::MAX);
    assert_eq!(full, Full::new().with_data(u64::MAX));
}

#[test]
fn clone() {
    /// We have a custom clone implementation -> opt out
    #[bitfield(u64, clone = false)]
    struct Full {
        data: u64,
    }

    impl Clone for Full {
        fn clone(&self) -> Self {
            Self::new().with_data(self.data())
        }
    }

    impl Copy for Full {}

    let full = Full::new().with_data(123);
    let full_copy = full;
    assert_eq!(full.data(), full_copy.data());
    assert_eq!(full.data(), full.clone().data());
}

#[test]
fn clone_cfg() {
    /// We opt in for clone/copy implementation, via a cfg.
    #[bitfield(u64, clone = cfg(test))]
    struct Full {
        data: u64,
    }

    let full = Full::new().with_data(123);
    let full_copy = full;
    assert_eq!(full.data(), full_copy.data());
    assert_eq!(full.data(), full.clone().data());
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

// a dummy defmt logger and timestamp implementation, for testing
mod defmt_logger {
    #[defmt::global_logger]
    struct Logger;

    unsafe impl defmt::Logger for Logger {
        fn acquire() {}
        unsafe fn flush() {}
        unsafe fn release() {}
        unsafe fn write(_bytes: &[u8]) {}
    }

    defmt::timestamp!("");
}

#[test]
fn defmt() {
    #[bitfield(u64, defmt = true)]
    struct Full {
        data: u64,
    }

    let full = Full::new().with_data(123);
    defmt::println!("{:?}", full);
}

#[test]
fn defmt_primitives() {
    #[bitfield(u128, defmt = true)]
    struct Unsigned {
        a: bool,
        #[bits(7)]
        __: u8,
        b: u8,
        c: u16,
        d: u32,
        e: u64,
    }

    defmt::println!("{}", Unsigned::new());

    #[bitfield(u128, defmt = true)]
    struct FullUnsigned {
        data: u128,
    }

    defmt::println!("{}", FullUnsigned::new());

    #[bitfield(u128, defmt = true)]
    struct Signed {
        a: bool,
        #[bits(7)]
        __: u8,
        b: i8,
        c: i16,
        d: i32,
        e: i64,
    }

    defmt::println!("{}", Signed::new());

    #[bitfield(u128, defmt = true)]
    struct FullSigned {
        data: i128,
    }

    defmt::println!("{}", FullSigned::new());

    #[bitfield(u128, defmt = true)]
    struct Size {
        #[bits(64)]
        a: usize,
        #[bits(64)]
        b: usize,
    }

    defmt::println!("{}", Size::new());

    const fn f32_from_bits(_bits: u32) -> f32 {
        // just for testing
        0.0
    }

    const fn f64_from_bits(_bits: u64) -> f64 {
        // just for testing
        0.0
    }

    #[bitfield(u128, defmt = true)]
    struct Float {
        __: u32,
        #[bits(32, from = f32_from_bits, access = RO)]
        a: f32,
        #[bits(64, from = f64_from_bits, access = RO)]
        b: f64,
    }

    defmt::println!("{}", Float::new());
}

#[test]
fn debug_cfg() {
    /// We have a custom debug implementation -> opt out
    #[bitfield(u64, debug = cfg(test), defmt = cfg(target_has_atomic = "64"))]
    struct Full {
        data: u64,
    }

    let full = Full::new().with_data(123);
    println!("{full:?}");
}

#[test]
fn positive() {
    #[bitfield(u32)]
    struct MyBitfield {
        #[bits(3)]
        positive: u32,
        #[bits(29)]
        __: (),
    }

    let v = MyBitfield::new().with_positive(0);
    assert_eq!(v.positive(), 0);
    let v = MyBitfield::new().with_positive(1);
    assert_eq!(v.positive(), 1);
    let v = MyBitfield::new().with_positive(7);
    assert_eq!(v.positive(), 7);
}

#[test]
fn negative() {
    #[bitfield(u32)]
    struct MyBitfield {
        #[bits(3)]
        negative: i32,
        #[bits(29)]
        __: (),
    }

    let v = MyBitfield::new().with_negative(-3);
    assert_eq!(v.negative(), -3);
    let v = MyBitfield::new().with_negative(0);
    assert_eq!(v.negative(), 0);
    let v = MyBitfield::new().with_negative(3);
    assert_eq!(v.negative(), 3);
    let v = MyBitfield::new().with_negative(-4);
    assert_eq!(v.negative(), -4);
}

#[test]
#[should_panic]
#[cfg(debug_assertions)]
fn negative_pos_overflow() {
    #[bitfield(u32)]
    struct MyBitfield {
        #[bits(3)]
        negative: i32,
        #[bits(29)]
        __: (),
    }

    MyBitfield::new().with_negative(4);
}

#[test]
#[should_panic]
#[cfg(debug_assertions)]
fn negative_neg_overflow() {
    #[bitfield(u32)]
    struct MyBitfield {
        #[bits(3)]
        negative: i32,
        #[bits(29)]
        __: (),
    }

    MyBitfield::new().with_negative(-5);
}

#[test]
fn checked_overflow() {
    #[bitfield(u32)]
    struct MyBitfield {
        #[bits(3)]
        negative: i32,
        #[bits(29)]
        __: (),
    }

    assert!(MyBitfield::new().with_negative_checked(4).is_err());
    assert!(MyBitfield::new().with_negative_checked(-5).is_err());
}

#[test]
fn negative_signed() {
    #[bitfield(u64)]
    struct MyBitfield {
        negative: i32,
        #[bits(10)]
        positive: u16,
        #[bits(22)]
        __: u32,
    }

    let val = MyBitfield::new()
        .with_negative(-1)
        .with_positive(0b11_1111_1111);
    assert_eq!(val.negative(), -1);
    assert_eq!(val.positive(), 0b11_1111_1111);
}

#[test]
fn entirely_negative() {
    #[bitfield(u32)]
    struct MyBitfield {
        negative: i32,
    }

    let v = MyBitfield::new().with_negative(-3);
    assert_eq!(v.negative(), -3);
    let v = MyBitfield::new().with_negative(0);
    assert_eq!(v.negative(), 0);
    let v = MyBitfield::new().with_negative(3);
    assert_eq!(v.negative(), 3);
    let v = MyBitfield::new().with_negative(i32::MIN);
    assert_eq!(v.negative(), i32::MIN);
    let v = MyBitfield::new().with_negative(i32::MAX);
    assert_eq!(v.negative(), i32::MAX);
}

#[test]
fn custom() {
    #[bitfield(u16)]
    #[derive(PartialEq, Eq)]
    struct Bits {
        /// Supports any type, with default/to/from expressions
        /// - into/from call Bits::into_bits/Bits::from_bits if nothing else is specified
        /// - default falls back to calling Bits::from_bits with 0
        #[bits(13, default = CustomEnum::B, from = CustomEnum::my_from_bits)]
        custom: CustomEnum,
        // Padding with default
        #[bits(3)]
        __: (),
    }

    #[derive(Debug, PartialEq, Eq)]
    #[repr(u16)]
    enum CustomEnum {
        A = 0,
        B = 1,
        C = 2,
    }
    impl CustomEnum {
        // This has to be a const fn
        const fn into_bits(self) -> u16 {
            self as _
        }
        const fn my_from_bits(value: u16) -> Self {
            match value {
                0 => Self::A,
                1 => Self::B,
                _ => Self::C,
            }
        }
    }
}

#[test]
fn defaults() {
    #[bitfield(u16)]
    #[derive(PartialEq, Eq)]
    struct MyBitfield {
        /// Interpreted as 1-bit flag, with custom default
        #[bits(default = true)]
        flag: bool,
        /// Supports any type, with default/to/from expressions (that are const eval)
        /// - into/from call #ty::into_bits/#ty::from_bits if nothing else is specified
        #[bits(13, default = CustomEnum::B, from = CustomEnum::my_from_bits)]
        custom: CustomEnum,
        // Padding with default
        #[bits(2, default = 0b10)]
        __: (),
    }

    /// A custom enum
    #[derive(Debug, PartialEq, Eq)]
    #[repr(u8)]
    enum CustomEnum {
        A = 0,
        B = 1,
        C = 2,
    }
    impl CustomEnum {
        // This has to be const eval
        const fn into_bits(self) -> u8 {
            self as _
        }
        const fn my_from_bits(value: u8) -> Self {
            match value {
                0 => Self::A,
                1 => Self::B,
                _ => Self::C,
            }
        }
    }

    // Uses defaults
    let val = MyBitfield::new();

    assert_eq!(val.flag(), true);
    assert_eq!(val.custom(), CustomEnum::B);
    assert_eq!(val.0 >> 14, 0b10); // padding
}

#[test]
fn default_padding() {
    #[bitfield(u32)]
    struct MyBitfield {
        value: u16,
        #[bits(15, default = 0xfff)]
        __: (),
        #[bits(default = true)]
        __: bool,
    }
    let v = MyBitfield::new().with_value(0xff);

    assert_eq!(v.0, 0x8fff_00ff);
}

#[test]
fn lsb_order() {
    #[bitfield(u32, order=lsb)]
    struct MyBitfield {
        short: u16,
        #[bits(8)]
        __: (),
        byte: u8,
    }

    let v = MyBitfield::new().with_short(0xe11e).with_byte(0xf0);

    assert_eq!(v.0, 0xf0_00_e11e);
}

#[test]
fn msb_order() {
    #[bitfield(u32, order=msb)]
    struct MyBitfield {
        short: u16,
        #[bits(8)]
        __: (),
        byte: u8,
    }

    let v = MyBitfield::new().with_short(0xe11e).with_byte(0xf0);

    assert_eq!(v.0, 0xe11e_00_f0);
}

#[test]
fn nested() {
    #[bitfield(u8)]
    #[derive(PartialEq)]
    struct Child {
        contents: u8,
    }
    #[bitfield(u16)]
    #[derive(PartialEq)]
    struct Parent {
        #[bits(8)]
        child: Child,
        other: u8,
    }
    let child = Child::new().with_contents(0xff);
    let parent = Parent::new().with_child(child);
    assert_eq!(child.into_bits(), 0xff);
    assert_eq!(parent.into_bits(), 0xff);
}

#[test]
fn raw() {
    #[bitfield(u8)]
    #[derive(PartialEq)]
    struct Raw {
        r#type: u8,
    }
    let raw = Raw::new().with_type(0xff);
    assert_eq!(raw.r#type(), 0xff);
    assert_eq!(raw.into_bits(), 0xff);
}

#[test]
fn custom_inner() {
    #[bitfield(u32, repr = CustomInner, from = CustomInner::from_inner, into = CustomInner::to_inner)]
    #[derive(PartialEq, Eq)]
    struct MyBitfield {
        data: u32,
    }

    #[derive(PartialEq, Eq, Clone, Copy, Debug)]
    #[repr(transparent)]
    struct CustomInner(u32);

    impl CustomInner {
        const fn to_inner(self) -> u32 {
            self.0
        }

        const fn from_inner(inner: u32) -> Self {
            Self(inner)
        }
    }

    let my_bitfield = MyBitfield::new();
    assert_eq!(my_bitfield, MyBitfield::from_bits(CustomInner(0)));
    assert_eq!(my_bitfield.into_bits(), CustomInner(0));
}

#[test]
fn default_without_setter() {
    use endian_num::le16;

    #[bitfield(u16, repr = le16, from = le16::from_ne, into = le16::to_ne)]
    struct Test {
        #[bits(14)]
        f3: u16,
        _reserved: bool, // no setter
        #[bits(1, access = RO)] // no setter
        reserved: bool,
    }
}

#[test]
fn default_msb_padding_default_value() {
    #[bitfield(u8, order = Msb)]
    struct MyMsbByte {
        #[bits(4, default = 0b1111)]
        __padding: usize,
        #[bits(4, default = 0b1010)]
        kind: usize,
    }
    let my_byte_msb = MyMsbByte::new();
    let val: u8 = my_byte_msb.into();
    assert_eq!(val, 0b1111_1010);
}

#[test]
fn default_lsb_padding_default_value() {
    #[bitfield(u8, order = Lsb)]
    struct MyMsbByte {
        #[bits(4, default = 0b1111)]
        __padding: usize,
        #[bits(4, default = 0b1010)]
        kind: usize,
    }
    let my_byte_msb = MyMsbByte::new();
    let val: u8 = my_byte_msb.into();
    assert_eq!(val, 0b1010_1111);
}

#[test]
fn hash() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    #[bitfield(u32, hash = true)]
    struct MyBitfield {
        data: u16,
        __: u8,
        #[bits(8)]
        extra: u8,
    }

    let mut hasher = DefaultHasher::new();
    MyBitfield::new()
        .with_data(0x1234)
        .with_extra(0x56)
        .hash(&mut hasher);
    let hash = hasher.finish();

    let mut hasher = DefaultHasher::new();
    MyBitfield::from_bits(0x56ee_1234).hash(&mut hasher);
    let other_hash = hasher.finish();

    assert_eq!(hash, other_hash, "Padding should not affect hash");

    let mut hasher = DefaultHasher::new();
    MyBitfield::new()
        .with_data(0x1234)
        .with_extra(0x57)
        .hash(&mut hasher);
    let other_hash = hasher.finish();
    assert_ne!(hash, other_hash, "Hash should change when data changes");
}

#[test]
fn custom_type_wo() {
    #[derive(Copy, Clone, Debug)]
    pub enum BlockState {
        Nil,
        Offset,
    }
    impl BlockState {
        const fn from_bits(val: u8) -> Self {
            match val {
                0 => Self::Nil,
                1 => Self::Offset,
                _ => unreachable!(),
            }
        }

        const fn into_bits(self) -> u8 {
            self as _
        }
    }
    #[bitfield(u64, clone = false, debug = false)]
    #[derive(Debug, Copy, Clone)]
    pub struct Block {
        #[bits(64, access = WO)]
        pub bstate: BlockState,
    }
}

#[test]
fn bitenum() {
    #[bitenum(all = true)]
    #[derive(PartialEq, Eq, Hash, Debug)]
    #[repr(u8)]
    enum MyEnum {
        #[fallback]
        A = 0,
        B = 1,
        C = 2,
        D = 3,
    }
    let e = MyEnum::from_bits(2);
    assert_eq!(e, MyEnum::C);
    let e = MyEnum::from_bits(4);
    assert_eq!(e, MyEnum::A);
    let bits = MyEnum::B.into_bits();
    assert_eq!(bits, 1);
    assert_eq!(MyEnum::all(), [MyEnum::A, MyEnum::B, MyEnum::C, MyEnum::D]);
}

#[allow(unexpected_cfgs)]
#[test]
fn bitnum_cfg() {
    #[bitenum(all = true)]
    #[derive(PartialEq, Eq, Hash, Debug)]
    #[repr(u8)]
    enum MyEnum {
        #[fallback]
        A = 0,
        B = 1,
        #[cfg(true)]
        C = 2,
        #[cfg(feature = "unknown")]
        D = 3,
    }
    let e = MyEnum::from_bits(2);
    assert_eq!(e, MyEnum::C);
    let e = MyEnum::from_bits(4);
    assert_eq!(e, MyEnum::A);
    let bits = MyEnum::B.into_bits();
    assert_eq!(bits, 1);
    assert_eq!(MyEnum::all(), [MyEnum::A, MyEnum::B, MyEnum::C]);
}

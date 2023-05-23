use std::fmt;

use bitfield_struct::bitfield;

#[test]
fn members() {
    /// A test bitfield with documentation
    #[bitfield(u64)]
    struct MyBitfield {
        /// defaults to 16 bits for u16
        int: u16,
        /// interpreted as 1 bit flag, with a custom default value
        #[bits(default = true)]
        flag: bool,
        /// custom bit size
        #[bits(1)]
        tiny: u8,
        /// sign extend for signed integers
        #[bits(13)]
        negative: i16,
        /// supports any type, with `into`/`from` expressions (that are const eval)
        ///
        /// the field is initialized with 0 (passed into `from`) if not specified otherwise
        #[bits(16, into = this as _, from = CustomEnum::from_bits(this))]
        custom: CustomEnum,
        /// public field -> public accessor functions
        #[bits(12)]
        pub public: usize,
        /// padding
        #[bits(5)]
        _p: (),
    }

    /// A custom enum
    #[derive(Debug, PartialEq, Eq)]
    #[repr(u64)]
    enum CustomEnum {
        A = 0,
        B = 1,
        C = 2,
    }
    impl CustomEnum {
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
        .with_public(2);

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

#[test]
fn positive() {
    #[bitfield(u32)]
    struct MyBitfield {
        #[bits(3)]
        positive: u32,
        #[bits(29)]
        _p: (),
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
        _p: (),
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

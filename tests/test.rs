use std::fmt;
use std::mem::{align_of, size_of};

use bitfield_struct::bitfield;

#[test]
fn members() {
    /// A test bitfield with documentation
    #[bitfield(ty = u64)]
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
    #[repr(u8)]
    enum CustomEnum {
        A = 0,
        B = 1,
        C = 2,
    }
    impl From<[u8; 2]> for CustomEnum {
        fn from(value: [u8; 2]) -> Self {
            match value[0] {
                0 => Self::A,
                1 => Self::B,
                _ => Self::C,
            }
        }
    }
    impl From<CustomEnum> for [u8; 2] {
        fn from(value: CustomEnum) -> Self {
            [value as _, 0]
        }
    }

    let mut val = MyBitfield::new()
        .with_int(3 << 15)
        .with_flag(true)
        .with_tiny(1)
        .with_negative(-3)
        .with_custom(CustomEnum::B)
        .with_public((1 << MyBitfield::PUBLIC_BITS) - 1);

    println!("{val:?}");

    let raw: u64 = val.into();
    println!("{raw:b}");

    let raw: [u8; 8] = val.into();
    for v in raw {
        print!("{v:08b} ");
    }
    println!();

    assert_eq!(val.int(), 3 << 15);
    assert_eq!(val.flag(), true);
    assert_eq!(val.negative(), -3);
    assert_eq!(val.tiny(), 1);
    assert_eq!(val.custom(), CustomEnum::B);
    assert_eq!(val.public(), (1 << MyBitfield::PUBLIC_BITS) - 1);

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
    #[bitfield(ty = u64)]
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
    #[bitfield(ty = u64, debug = false)]
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
fn custom_size() {
    /// We have a custom debug implementation -> opt out
    #[bitfield(bytes = 9)]
    struct NoTy {
        data: u64,
        extra: u8,
    }

    let full = NoTy::new().with_data(123).with_extra(255);
    assert_eq!(full.data(), 123);
    assert_eq!(full.extra(), 255);
    assert_eq!(align_of::<NoTy>(), 1);
    assert_eq!(size_of::<NoTy>(), 9);
    println!("{full:?}");
}

use bitfield_struct::bitfield;

/// A test bitfield with documentation
#[bitfield(u64)]
struct PageTableEntry {
    /// defaults to 32 bits for u32
    addr: u32,

    /// public field -> public accessor functions
    #[bits(12)]
    pub size: usize,

    /// padding
    #[bits(5)]
    _p: u8,

    #[bits(1)]
    bug: u8,

    /// interpreted as 1 bit flag
    present: bool,

    /// sign extend for signed integers
    #[bits(13)]
    negative: i16,
}

#[bitfield(u64)]
#[derive(PartialEq, Eq)]
struct Full {
    data: u64,
}

#[test]
fn basics() {
    let pte = PageTableEntry::new()
        .with_addr(3 << 31)
        .with_size(2)
        .with_present(false)
        .with_negative(-3);
    let value: u64 = pte.into();
    println!("{:b}", value);
    assert_eq!(pte.addr(), 3 << 31);
    assert_eq!(pte.size(), 2);
    assert_eq!(pte.present(), false);
    assert_eq!(pte.negative(), -3);

    let mut pte = pte.with_present(true);
    assert_eq!(pte.present(), true);
    pte.set_size(1);
    assert_eq!(pte.size(), 1);

    let full = Full::new().with_data(u64::MAX);
    assert_eq!(full.data(), u64::MAX);
    assert!(full == Full::new().with_data(u64::MAX));
}

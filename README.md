# Bitfield Struct

[![Crate](https://img.shields.io/crates/v/bitfield-struct.svg)](https://crates.io/crates/bitfield-struct)
[![API](https://docs.rs/bitfield-struct/badge.svg)](https://docs.rs/bitfield-struct)

Procedural macro for bitfields that allows specifying bitfields as structs.
As this library provides a procedural macro, it has no runtime dependencies and works for `no-std`.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
bitfield-struct = "0.2"
```

## Example

```rs
use bitfield_struct::bitfield;

#[bitfield(u64)]
#[derive(Default, PartialEq, Eq)] // Attributes are also applied
struct PageTableEntry {
    /// defaults to 32 bits for u32
    addr: u32,

    /// public field -> public accessor functions
    #[bits(12)]
    pub size: usize,

    /// padding: No accessor functions are generated for fields beginning with `_`.
    #[bits(6)]
    _p: u8,

    /// interpreted as 1 bit flag
    present: bool,

    /// sign extend for signed integers
    #[bits(13)]
    negative: i16,
}
```

The macro generates three accessor functions for each field.
Each accessor also inherits the documentation of its field.

The signatures for `addr` are:

```rs
// generated struct
struct PageTableEntry(u64);
impl PageTableEntry {
    const fn new() -> Self { Self(0) }

    const ADDR_BITS: usize = 32;
    const ADDR_OFFSET: usize = 0;

    const fn with_addr(self, value: u32) -> Self { /* ... */ }
    const fn addr(&self) -> u32 { /* ... */ }
    fn set_addr(&mut self, value: u32) { /* ... */ }

    // other field ...
}
// generated trait implementations
impl From<u64> for PageTableEntry { /* ... */ }
impl From<PageTableEntry> for u64 { /* ... */ }
impl Debug for PageTableEntry { /* ... */ }
```

This generated bitfield can then be used as follows.

```rs
let mut pte = PageTableEntry::new()
    .with_addr(3 << 31)
    .with_size(2)
    .with_present(false)
    .with_negative(-3);

println!("{pte:?}");
assert!(pte.addr() == 3 << 31);

pte.set_size(1);

let value: u64 = pte.into();
println!("{value:b}");
```

## `fmt::Debug`

This macro automatically creates a suitable `fmt::Debug` implementation
similar to the ones created for normal structs by `#[derive(Debug)]`.
You can disable it with the extra debug argument.

```rs
#[bitfield(u64, debug = false)]
struct CustomDebug {
    data: u64
}

impl fmt::Debug for CustomDebug {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{:x}", self.data())
    }
}
```

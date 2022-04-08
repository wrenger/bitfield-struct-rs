# Bitfield Struct

[![Crate](https://img.shields.io/crates/v/bitfield-struct.svg)](https://crates.io/crates/bitfield-struct)
[![API](https://docs.rs/bitfield-struct/badge.svg)](https://docs.rs/bitfield-struct)

Procedural macro for bitfields that allows specifying bitfields as structs.
As this library provides a procedural-macro it has no runtime dependencies and works for `no-std`.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
bitfield-struct = "0.1.6"
```

## Example

```rust
#[bitfield(u64)]
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

The signatures for `addr` for example are:

```rust
struct PageTableEntry(u64);
impl PageTableEntry {
    const fn new() -> Self { /* ... */ }

    const fn with_addr(self, value: u32) -> Self { /* ... */ }
    const fn addr(&self) -> u32 { /* ... */ }
    fn set_addr(&mut self, value: u32) { /* ... */ }

    // other members ...
}
impl From<u64> for PageTableEntry { /* ... */ }
impl From<PageTableEntry> for u64 { /* ... */ }
```

This generated bitfield then can be used as follows.

```rust
let pte = PageTableEntry::new()
    .with_addr(3 << 31)
    .with_size(2)
    .with_present(false)
    .with_negative(-3);

println!("{}", pte.addr());

pte.set_size(1);

let value: u64 = pte.into();
println!("{:b}", value);
```

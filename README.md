# Bitfield Struct

[![Crate](https://img.shields.io/crates/v/bitfield-struct.svg)](https://crates.io/crates/bitfield-struct)
[![API](https://docs.rs/bitfield-struct/badge.svg)](https://docs.rs/bitfield-struct)

Procedural macro for declarative defining bitfields similar to structs.
As this library provides a procedural macro, it has no runtime dependencies and works for `no-std`.

- Supports bool flags, raw integers, and every custom type convertible into integers (structs/enums)
- Ideal for driver/OS/embedded development (defining HW registers/structures)
- Generates minimalistic, pure, safe rust functions
- Compile-time checks for type and field sizes
- Rust-analyzer friendly (carries over documentation to accessor functions)
- Exports field offsets and sizes as constants (useful for const asserts)
- Generation of `fmt::Debug`

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
bitfield-struct = "0.4"
```

## Basics

Let's begin with a simple example.
Suppose we want to store multiple data inside a single Byte, as shown below:

<table>
  <tr>
    <td>7</td>
    <td>6</td>
    <td>5</td>
    <td>4</td>
    <td>3</td>
    <td>3</td>
    <td>1</td>
    <td>0</td>
  </tr>
  <tr>
    <td>P</td>
    <td colspan="2">Level</td>
    <td>S</td>
    <td colspan="4">Kind</td>
  </tr>
</table>

This crate generates a nice wrapper type that makes it easy to do this:

```rust
/// Define your type like this with the bitfield attribute
#[bitfield(u8)]
struct MyByte {
    /// The first field occupies the least significant bits
    #[bits(4)]
    kind: usize,
    /// Booleans are 1 bit large
    system: bool,
    /// The bits attribute specifies the bit size of this field
    #[bits(2)]
    level: usize,
    /// The last field spans over the most significant bits
    present: bool
}
// The macro creates three accessor functions for each field:
// <name>, with_<name> and set_<name>
let my_byte = MyByte::new()
    .with_kind(15)
    .with_system(false)
    .with_level(3)
    .with_present(true);

assert!(my_byte.present());
```

## Features

Additionally, this crate has a few useful features, which are shown here in more detail.

The example below shows how attributes are carried over and how signed integers, padding, and custom types are handled.

```rust
/// A test bitfield with documentation
#[bitfield(u64)]
#[derive(PartialEq, Eq)] // <- Attributes after `bitfield` are carried over
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
// implement `From<u64>` and `Into<u64>` for `CustomEnum`!

// Usage:
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
```

The macro generates three accessor functions for each field.
Each accessor also inherits the documentation of its field.

The signatures for `int` are:

```rust
// generated struct
struct MyBitfield(u64);
impl MyBitfield {
    const fn new() -> Self { Self(0) }

    const INT_BITS: usize = 16;
    const INT_OFFSET: usize = 0;

    const fn with_int(self, value: u16) -> Self { /* ... */ }
    const fn int(&self) -> u16 { /* ... */ }
    fn set_int(&mut self, value: u16) { /* ... */ }

    // other field ...
}
// generated trait implementations
impl From<u64> for MyBitfield { /* ... */ }
impl From<MyBitfield> for u64 { /* ... */ }
impl Debug for MyBitfield { /* ... */ }
```

> Hint: You can use the rust-analyzer "Expand macro recursively" action to view the generated code.

## `fmt::Debug`

This macro automatically creates a suitable `fmt::Debug` implementation
similar to the ones created for normal structs by `#[derive(Debug)]`.
You can disable it with the extra debug argument.

```rust
#[bitfield(u64, debug = false)]
struct CustomDebug {
    data: u64
}
impl fmt::Debug for CustomDebug {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{:x}", self.data())
    }
}

let val = CustomDebug::new().with_data(123);
println!("{val:?}")
```

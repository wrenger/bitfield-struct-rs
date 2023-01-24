//! # Bitfield Struct
//!
//! Procedural macro for bitfields that allows specifying bitfields as structs.
//! As this library provides a procedural-macro it has no runtime dependencies and works for `no-std`.
//!
//! - Supports bool flags, raw integers, and every custom type convertible into integers (structs/enums)
//! - Ideal for driver/OS/embedded development (defining HW registers/structures)
//! - Generates minimalistic, pure, safe rust functions
//! - Compile-time checks for type and field sizes
//! - Rust-analyzer friendly (carries over documentation to accessor functions)
//! - Exports field offsets and sizes as constants (useful for const asserts)
//! - Generation of `fmt::Debug`
//!
//! ## Basics
//!
//! Let's begin with a simple example.</br>
//! Suppose we want to store multiple data inside a single Byte, as shown below:
//!
//! <table>
//!   <tr>
//!     <td>7</td>
//!     <td>6</td>
//!     <td>5</td>
//!     <td>4</td>
//!     <td>3</td>
//!     <td>3</td>
//!     <td>1</td>
//!     <td>0</td>
//!   </tr>
//!   <tr>
//!     <td>P</td>
//!     <td colspan="2">Level</td>
//!     <td>S</td>
//!     <td colspan="4">Kind</td>
//!   </tr>
//! </table>
//!
//! This crate is able to generate a nice wrapper type that makes it easy to do this:
//!
//! ```
//! # use bitfield_struct::bitfield;
//! /// Define your type like this with the bitfield attribute
//! #[bitfield(u8)]
//! struct MyByte {
//!     /// The first field occupies the least significant bits
//!     #[bits(4)]
//!     kind: usize,
//!     /// Booleans are 1 bit large
//!     system: bool,
//!     /// The bits attribute specifies the bit size of this field
//!     #[bits(2)]
//!     level: usize,
//!     /// The last field spans over the most significant bits
//!     present: bool
//! }
//! // The macro creates three accessor functions for each field:
//! // <name>, with_<name> and set_<name>
//! let my_byte = MyByte::new()
//!     .with_kind(15)
//!     .with_system(false)
//!     .with_level(3)
//!     .with_present(true);
//!
//! assert!(my_byte.present());
//! ```
//!
//! ## Features
//!
//! Additionally, this crate has a few useful features, which are shown here in more detail.
//!
//! The example below shows how attributes are carried over and how signed integers, padding, and custom types are handled.
//!
//! ```
//! # use bitfield_struct::bitfield;
//! /// A test bitfield with documentation
//! #[bitfield(u64)]
//! #[derive(PartialEq, Eq)] // <- Attributes after `bitfield` are carried over
//! struct MyBitfield {
//!     /// defaults to 16 bits for u16
//!     int: u16,
//!     /// interpreted as 1 bit flag
//!     flag: bool,
//!     /// custom bit size
//!     #[bits(1)]
//!     tiny: u8,
//!     /// sign extend for signed integers
//!     #[bits(13)]
//!     negative: i16,
//!     /// supports any type that implements `From<u64>` and `Into<u64>`
//!     #[bits(16)]
//!     custom: CustomEnum,
//!     /// public field -> public accessor functions
//!     #[bits(12)]
//!     pub public: usize,
//!     /// padding
//!     #[bits(5)]
//!     _p: u8,
//!     /// zero-sized members are ignored
//!     #[bits(0)]
//!     _completely_ignored: String,
//! }
//!
//! /// A custom enum
//! #[derive(Debug, PartialEq, Eq)]
//! #[repr(u64)]
//! enum CustomEnum {
//!     A = 0,
//!     B = 1,
//!     C = 2,
//! }
//! // implement `From<u64>` and `Into<u64>` for `CustomEnum`!
//! # impl From<u64> for CustomEnum {
//! #     fn from(value: u64) -> Self {
//! #         match value {
//! #             0 => Self::A,
//! #             1 => Self::B,
//! #             _ => Self::C,
//! #         }
//! #     }
//! # }
//! # impl From<CustomEnum> for u64 {
//! #     fn from(value: CustomEnum) -> Self {
//! #         value as _
//! #     }
//! # }
//!
//! // Usage:
//! let mut val = MyBitfield::new()
//!     .with_int(3 << 15)
//!     .with_flag(true)
//!     .with_tiny(1)
//!     .with_negative(-3)
//!     .with_custom(CustomEnum::B)
//!     .with_public(2);
//!
//! println!("{val:?}");
//! let raw: u64 = val.into();
//! println!("{raw:b}");
//!
//! assert_eq!(val.int(), 3 << 15);
//! assert_eq!(val.flag(), true);
//! assert_eq!(val.negative(), -3);
//! assert_eq!(val.tiny(), 1);
//! assert_eq!(val.custom(), CustomEnum::B);
//! assert_eq!(val.public(), 2);
//!
//! // const members
//! assert_eq!(MyBitfield::FLAG_BITS, 1);
//! assert_eq!(MyBitfield::FLAG_OFFSET, 16);
//!
//! val.set_negative(1);
//! assert_eq!(val.negative(), 1);
//! ```
//!
//! The macro generates three accessor functions for each field.
//! Each accessor also inherits the documentation of its field.
//!
//! The signatures for `int` are:
//!
//! ```ignore
//! // generated struct
//! struct MyBitfield(u64);
//! impl MyBitfield {
//!     const fn new() -> Self { Self(0) }
//!
//!     const INT_BITS: usize = 16;
//!     const INT_OFFSET: usize = 0;
//!
//!     const fn with_int(self, value: u16) -> Self { /* ... */ }
//!     const fn int(&self) -> u16 { /* ... */ }
//!     fn set_int(&mut self, value: u16) { /* ... */ }
//!
//!     // other field ...
//! }
//! // generated trait implementations
//! impl From<u64> for MyBitfield { /* ... */ }
//! impl From<MyBitfield> for u64 { /* ... */ }
//! impl Debug for MyBitfield { /* ... */ }
//! ```
//!
//! > Hint: You can use the rust-analyzer "Expand macro recursively" action to view the generated code.
//!
//! ## `fmt::Debug`
//!
//! This macro automatically creates a suitable `fmt::Debug` implementation
//! similar to the ones created for normal structs by `#[derive(Debug)]`.
//! You can disable it with the extra debug argument.
//!
//! ```
//! # use std::fmt;
//! # use bitfield_struct::bitfield;
//!
//! #[bitfield(u64, debug = false)]
//! struct CustomDebug {
//!     data: u64
//! }
//!
//! impl fmt::Debug for CustomDebug {
//!     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//!         write!(f, "0x{:x}", self.data())
//!     }
//! }
//!
//! let val = CustomDebug::new().with_data(123);
//! println!("{val:?}")
//! ```
//!

use proc_macro as pc;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::stringify;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::Token;

/// Creates a bitfield for this struct.
///
/// The arguments first, have to begin with the underlying type of the bitfield:
/// For example: `#[bitfield(u64)]`.
///
/// It can contain an extra `debug` argument for disabling the `Debug` trait
/// generation (`#[bitfield(u64, debug = false)]`).
#[proc_macro_attribute]
pub fn bitfield(args: pc::TokenStream, input: pc::TokenStream) -> pc::TokenStream {
    match bitfield_inner(args.into(), input.into()) {
        Ok(result) => result.into(),
        Err(e) => e.into_compile_error().into(),
    }
}

fn bitfield_inner(args: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let input = syn::parse2::<syn::ItemStruct>(input)?;
    let Params { ty, bits, debug } =
        syn::parse2::<Params>(args).map_err(|e| unsupported_param(e, input.span()))?;

    let span = input.fields.span();
    let name = input.ident;
    let name_str = name.to_string();
    let vis = input.vis;
    let attrs: TokenStream = input.attrs.iter().map(ToTokens::to_token_stream).collect();

    let syn::Fields::Named(fields) = input.fields else {
        return Err(syn::Error::new(span, "only named fields are supported"));
    };

    let mut offset = 0;
    let mut members = Vec::with_capacity(fields.named.len());
    for field in fields.named {
        let f = Member::new(ty.clone(), field, offset)?;
        offset += f.bits;
        members.push(f);
    }

    if offset < bits {
        return Err(syn::Error::new(
            span,
            format!(
                "The bitfiled size ({bits} bits) has to be equal to the sum of its members ({offset} bits)!. \
                You might have to add padding (a {} bits large member prefixed with \"_\").",
                bits - offset
            ),
        ));
    }
    if offset > bits {
        return Err(syn::Error::new(
            span,
            format!(
                "The size of the members ({offset} bits) is larger than the type ({bits} bits)!."
            ),
        ));
    }

    let debug_impl = if debug {
        let debug_fields = members.iter().map(|m| m.debug());
        quote! {
            impl core::fmt::Debug for #name {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.debug_struct(#name_str)
                        #( #debug_fields )*
                        .finish()
                }
            }
        }
    } else {
        Default::default()
    };

    Ok(quote! {
        #attrs
        #[derive(Copy, Clone)]
        #[repr(transparent)]
        #vis struct #name(#ty);

        impl #name {
            #vis const fn new() -> Self {
                Self(0)
            }

            #( #members )*
        }

        impl From<#ty> for #name {
            fn from(v: #ty) -> Self {
                Self(v)
            }
        }
        impl From<#name> for #ty {
            fn from(v: #name) -> #ty {
                v.0
            }
        }

        #debug_impl
    })
}

/// Distinguish between different types for code generation.
///
/// We need this to make accessor functions for bool and ints const.
/// As soon as we have const conversion traits, we can simply switch to `TryFrom` and don't have to generate different code.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TypeClass {
    Bool,
    Int,
    Other,
}

struct Member {
    base_ty: syn::Type,
    attrs: Vec<syn::Attribute>,
    ty: syn::Type,
    class: TypeClass,
    bits: usize,
    ident: syn::Ident,
    vis: syn::Visibility,
    offset: usize,
}

impl Member {
    fn new(base_ty: syn::Type, f: syn::Field, offset: usize) -> syn::Result<Self> {
        let span = f.span();

        let syn::Field {
            mut attrs,
            vis,
            ident,
            ty,
            ..
        } = f;

        let ident = ident.ok_or_else(|| syn::Error::new(span, "Not supported"))?;

        let (class, bits) = bits(&attrs, &ty)?;
        // remove our attribute
        attrs.retain(|a| !a.path.is_ident("bits"));

        Ok(Self {
            base_ty,
            attrs,
            ty,
            class,
            bits,
            ident,
            vis,
            offset,
        })
    }

    fn debug(&self) -> TokenStream {
        let ident_str = self.ident.to_string();
        if self.bits > 0 && !ident_str.starts_with('_') {
            let ident = &self.ident;
            quote!(.field(#ident_str, &self.#ident()))
        } else {
            Default::default()
        }
    }
}

impl ToTokens for Member {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self {
            base_ty,
            attrs,
            ty,
            class,
            bits,
            ident,
            vis,
            offset,
        } = self;
        let ident_str = ident.to_string();

        // Skip zero sized and padding members
        if self.bits == 0 || ident_str.starts_with('_') {
            return Default::default();
        }

        let with_ident = format_ident!("with_{ident}");
        let set_ident = format_ident!("set_{ident}");
        let bits_ident = format_ident!("{}_BITS", ident_str.to_uppercase());
        let offset_ident = format_ident!("{}_OFFSET", ident_str.to_uppercase());

        let location = format!("\n\nBits: {offset}..{}", offset + bits);

        let doc: TokenStream = attrs
            .iter()
            .filter(|a| !a.path.is_ident("bits"))
            .map(ToTokens::to_token_stream)
            .collect();

        let general = quote! {
            const #bits_ident: usize = #bits;
            const #offset_ident: usize = #offset;

            #doc
            #[doc = #location]
            #vis fn #set_ident(&mut self, value: #ty) {
                *self = self.#with_ident(value);
            }
        };

        let mask: u128 = !0 >> (u128::BITS as usize - bits);
        let mask = syn::LitInt::new(&format!("0x{mask:x}"), Span::mixed_site());

        let code = match class {
            TypeClass::Bool => quote! {
                #general

                #doc
                #[doc = #location]
                #vis const fn #with_ident(self, value: #ty) -> Self {
                    Self(self.0 & !(1 << #offset) | (value as #base_ty & 1) << #offset)
                }
                #doc
                #[doc = #location]
                #vis const fn #ident(&self) -> #ty {
                    ((self.0 >> #offset) & 1) != 0
                }
            },
            TypeClass::Int => quote! {
                #general

                #doc
                #[doc = #location]
                #vis const fn #with_ident(self, value: #ty) -> Self {
                    debug_assert!(value <= #mask);
                    Self(self.0 & !(#mask << #offset) | (value as #base_ty & #mask) << #offset)
                }
                #doc
                #[doc = #location]
                #vis const fn #ident(&self) -> #ty {
                    (((self.0 >> #offset) as #ty) << #ty::BITS as usize - #bits) >> #ty::BITS as usize - #bits
                }
            },
            TypeClass::Other => quote! {
                #general

                #doc
                #[doc = #location]
                #vis fn #with_ident(self, value: #ty) -> Self {
                    let value: #base_ty = value.into();
                    debug_assert!(value <= #mask);
                    Self(self.0 & !(#mask << #offset) | (value & #mask) << #offset)
                }
                #doc
                #[doc = #location]
                #vis fn #ident(&self) -> #ty {
                    (((self.0 >> #offset) << #base_ty::BITS as usize - #bits) >> #base_ty::BITS as usize - #bits).into()
                }
            },
        };
        tokens.extend(code);
    }
}

/// Parses the `bits` attribute that allows specifying a custom number of bits.
fn bits(attrs: &[syn::Attribute], ty: &syn::Type) -> syn::Result<(TypeClass, usize)> {
    fn malformed(mut e: syn::Error, attr: &syn::Attribute) -> syn::Error {
        e.combine(syn::Error::new(attr.span(), "malformed #[bits] attribute"));
        e
    }

    for attr in attrs {
        match attr {
            syn::Attribute {
                style: syn::AttrStyle::Outer,
                path,
                tokens,
                ..
            } if path.is_ident("bits") => {
                let bits = attr
                    .parse_args::<syn::LitInt>()
                    .map_err(|e| malformed(e, attr))?
                    .base10_parse()
                    .map_err(|e| malformed(e, attr))?;

                return if bits == 0 {
                    Ok((TypeClass::Other, 0))
                } else if let Ok((class, size)) = type_bits(ty) {
                    if bits <= size {
                        Ok((class, bits))
                    } else {
                        Err(syn::Error::new(tokens.span(), "overflowing field type"))
                    }
                } else {
                    Ok((TypeClass::Other, bits))
                };
            }
            _ => {}
        }
    }

    // Fallback to type size
    type_bits(ty)
}

/// Returns the number of bits for a given type
fn type_bits(ty: &syn::Type) -> syn::Result<(TypeClass, usize)> {
    let syn::Type::Path(syn::TypePath{ path, .. }) = ty else {
        return Err(syn::Error::new(ty.span(), "unsupported type"))
    };
    let Some(ident) = path.get_ident() else {
        return Err(syn::Error::new(ty.span(), "unsupported type"))
    };
    if ident == "bool" {
        return Ok((TypeClass::Bool, 1));
    }
    macro_rules! integer {
        ($ident:ident => $($ty:ident),*) => {
            match ident {
                $(_ if ident == stringify!($ty) => Ok((TypeClass::Int, $ty::BITS as _)),)*
                _ => Err(syn::Error::new(ty.span(), "unsupported type"))
            }
        };
    }
    integer!(ident => u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize)
}

struct Params {
    ty: syn::Type,
    bits: usize,
    debug: bool,
}

impl Parse for Params {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let Ok(ty) = syn::Type::parse(input) else {
            return Err(syn::Error::new(input.span(), "unknown type"));
        };
        let (class, bits) = type_bits(&ty)?;
        if class != TypeClass::Int {
            return Err(syn::Error::new(input.span(), "unsupported type"));
        }

        // try parse additional debug arg
        let debug = if <Token![,]>::parse(input).is_ok() {
            let ident = Ident::parse(input)?;

            if ident != "debug" {
                return Err(syn::Error::new(ident.span(), "unknown argument"));
            }
            <Token![=]>::parse(input)?;

            syn::LitBool::parse(input)?.value
        } else {
            true
        };

        Ok(Params { bits, ty, debug })
    }
}

fn unsupported_param<T>(mut e: syn::Error, arg: T) -> syn::Error
where
    T: syn::spanned::Spanned,
{
    e.combine(syn::Error::new(
        arg.span(),
        "unsupported #[bitfield] argument",
    ));
    e
}

#[cfg(test)]
mod test {
    use quote::quote;

    use crate::Params;

    #[test]
    fn parse_args() {
        let args = quote! {
            usize
        };
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bits == usize::BITS as usize && params.debug == true);

        let args = quote! {
            u32, debug = false
        };
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bits == u32::BITS as usize && params.debug == false);
    }
}

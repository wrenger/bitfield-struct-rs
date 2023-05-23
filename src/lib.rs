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
//! Let's begin with a simple example.<br>
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
//!     /// interpreted as 1 bit flag, with a custom default value
//!     #[bits(default = true)]
//!     flag: bool,
//!     /// custom bit size
//!     #[bits(1)]
//!     tiny: u8,
//!     /// sign extend for signed integers
//!     #[bits(13)]
//!     negative: i16,
//!     /// supports any type, with `into`/`from` expressions (that are const eval)
//!     ///
//!     /// the field is initialized with 0 (passed into `from`) if not specified otherwise
//!     #[bits(16, into = this as _, from = CustomEnum::from_bits(this))]
//!     custom: CustomEnum,
//!     /// public field -> public accessor functions
//!     #[bits(12)]
//!     pub public: usize,
//!     /// padding
//!     #[bits(5)]
//!     _p: u8,
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
//! impl CustomEnum {
//!     // This has to be const eval
//!     const fn from_bits(value: u64) -> Self {
//!         match value {
//!             0 => Self::A,
//!             1 => Self::B,
//!             _ => Self::C,
//!         }
//!     }
//! }
//!
//! // Usage:
//! let mut val = MyBitfield::new()
//!     .with_int(3 << 15)
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
    let Params { ty, bits, debug } = syn::parse2::<Params>(args)?;

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

    let defaults = members.iter().map(|m| m.default());

    Ok(quote! {
        #attrs
        #[derive(Copy, Clone)]
        #[repr(transparent)]
        #vis struct #name(#ty);

        impl #name {
            /// Creates a new zero initialized bitfield.
            #vis const fn new() -> Self {
                Self(0)
                #( #defaults )*
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

/// Represents a member where accessor functions should be generated for.
struct Member {
    offset: usize,
    bits: usize,
    base_ty: syn::Type,
    inner: Option<MemberInner>,
}

struct MemberInner {
    ident: syn::Ident,
    ty: syn::Type,
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    default: TokenStream,
    into: TokenStream,
    from: TokenStream,
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
        let ignore = ident.to_string().starts_with('_');

        let Field {
            bits,
            ty,
            class: _,
            default,
            into,
            from,
        } = parse_field(&attrs, &ty, ignore)?;

        if bits > 0 && !ignore {
            if default.is_empty() || into.is_empty() || from.is_empty() {
                return Err(syn::Error::new(
                    ty.span(),
                    "Custom types require 'into', and 'from' in the #[bits] attribute",
                ));
            }

            // remove our attribute
            attrs.retain(|a| !a.path().is_ident("bits"));

            Ok(Self {
                offset,
                bits,
                base_ty,
                inner: Some(MemberInner {
                    ident,
                    ty,
                    attrs,
                    vis,
                    default,
                    into,
                    from,
                }),
            })
        } else {
            Ok(Self {
                offset,
                bits,
                base_ty,
                inner: None,
            })
        }
    }

    fn debug(&self) -> TokenStream {
        if let Some(inner) = &self.inner {
            let ident_str = inner.ident.to_string();
            let ident = &inner.ident;
            quote!(.field(#ident_str, &self.#ident()))
        } else {
            Default::default()
        }
    }

    fn default(&self) -> TokenStream {
        if let Some(inner) = &self.inner {
            let ident = &inner.ident;
            let with_ident = format_ident!("with_{ident}");
            let default = &inner.default;
            quote!(.#with_ident(#default))
        } else {
            Default::default()
        }
    }
}

impl ToTokens for Member {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self {
            offset,
            bits,
            base_ty,
            inner: Some(MemberInner { ident, ty, attrs, vis, default: _, into, from }),
        } = self else {
            return Default::default();
        };

        let ident_str = ident.to_string();

        let with_ident = format_ident!("with_{ident}");
        let set_ident = format_ident!("set_{ident}");
        let bits_ident = format_ident!("{}_BITS", ident_str.to_uppercase());
        let offset_ident = format_ident!("{}_OFFSET", ident_str.to_uppercase());

        let location = format!("\n\nBits: {offset}..{}", offset + bits);

        let doc: TokenStream = attrs
            .iter()
            .filter(|a| !a.path().is_ident("bits"))
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

        let bits = *bits as u32;
        let mask: u128 = !0 >> (u128::BITS - bits);
        let mask = syn::LitInt::new(&format!("0x{mask:x}"), Span::mixed_site());

        let code = quote! {
            #general

            #doc
            #[doc = #location]
            #vis const fn #with_ident(self, value: #ty) -> Self {
                let value: #base_ty = {
                    let this = value;
                    #into
                };
                debug_assert!(value <= #mask, "value out of bounds");
                Self(self.0 & !(#mask << #offset) | (value & #mask) << #offset)
            }
            #doc
            #[doc = #location]
            #vis const fn #ident(&self) -> #ty {
                let this = (self.0 >> #offset) & #mask;
                #from
            }
        };
        tokens.extend(code);
    }
}

/// Distinguish between different types for code generation.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TypeClass {
    /// Booleans with 1 bit size
    Bool,
    /// Unsigned ints with fixes sizes: u8, u64, ...
    UInt,
    /// Signed ints with fixes sizes: i8, i64, ...
    SInt,
    /// Custom types
    Other,
}

/// Field information, including the `bits` attribute
struct Field {
    bits: usize,
    ty: syn::Type,
    class: TypeClass,

    default: TokenStream,
    into: TokenStream,
    from: TokenStream,
}

/// Parses the `bits` attribute that allows specifying a custom number of bits.
fn parse_field(attrs: &[syn::Attribute], ty: &syn::Type, ignore: bool) -> syn::Result<Field> {
    fn malformed(mut e: syn::Error, attr: &syn::Attribute) -> syn::Error {
        e.combine(syn::Error::new(attr.span(), "malformed #[bits] attribute"));
        e
    }

    // Defaults for the different types
    let (class, ty_bits) = type_bits(ty);
    let mut ret = match class {
        TypeClass::Bool => Field {
            bits: ty_bits,
            ty: ty.clone(),
            class,
            default: quote!(false),
            into: quote!(this as _),
            from: quote!(this != 0),
        },
        TypeClass::SInt => Field {
            bits: ty_bits,
            ty: ty.clone(),
            class,
            default: quote!(0),
            into: TokenStream::new(),
            from: TokenStream::new(),
        },
        TypeClass::UInt => Field {
            bits: ty_bits,
            ty: ty.clone(),
            class,
            default: quote!(0),
            into: quote!(this as _),
            from: quote!(this as _),
        },
        TypeClass::Other => Field {
            bits: ty_bits,
            ty: ty.clone(),
            class,
            default: TokenStream::new(),
            into: TokenStream::new(),
            from: TokenStream::new(),
        },
    };

    // Find and parse the bits attribute
    for attr in attrs {
        match attr {
            syn::Attribute {
                style: syn::AttrStyle::Outer,
                meta: syn::Meta::List(syn::MetaList { path, tokens, .. }),
                ..
            } if path.is_ident("bits") => {
                let BitsAttr {
                    bits,
                    default,
                    into,
                    from,
                } = syn::parse2::<BitsAttr>(tokens.clone()).map_err(|e| malformed(e, attr))?;

                if let Some(bits) = bits {
                    if bits == 0 {
                        return Err(syn::Error::new(tokens.span(), "bits cannot bit 0"));
                    }
                    if ty_bits != 0 && bits > ty_bits {
                        return Err(syn::Error::new(tokens.span(), "overflowing field type"));
                    }
                    ret.bits = bits;
                }
                if ignore && (default.is_some() || into.is_some() || from.is_some()) {
                    return Err(syn::Error::new(
                        default.span(),
                        "'default', 'into', and 'from' are not (yet) supported on padding",
                    ));
                }

                if let Some(default) = default {
                    ret.default = default;
                }
                if let Some(into) = into {
                    ret.into = into;
                }
                if let Some(from) = from {
                    // Auto-conversion from zero
                    if ret.default.is_empty() {
                        ret.default = quote!({
                            let this = 0;
                            #from
                        });
                    }

                    ret.from = from;
                }
            }
            _ => {}
        }
    }

    if ret.bits == 0 {
        return Err(syn::Error::new(
            ty.span(),
            "Custom types and isize/usize require the size in the #[bits] attribute",
        ));
    }

    // Negative integers need some special handling...
    if !ignore && ret.class == TypeClass::SInt {
        let bits = ret.bits as u32;
        let mask: u128 = !0 >> (u128::BITS - bits);
        let mask = syn::LitInt::new(&format!("0x{mask:x}"), Span::mixed_site());
        if ret.into.is_empty() {
            // Bounds check and remove leading ones from negative values
            ret.into = quote! {{
                #[allow(unused_comparisons)]
                debug_assert!(if this >= 0 { this & !#mask == 0 } else { !this & !#mask == 0 }, "value out of bounds");
                (this & #mask) as _
            }};
        }
        if ret.from.is_empty() {
            // Sign extend negative values
            ret.from = quote! {{
                let shift = #ty::BITS - #bits;
                ((this as #ty) << shift) >> shift
            }};
        }
    }

    Ok(ret)
}

/// The bits attribute of the fields of a bitfield struct
struct BitsAttr {
    bits: Option<usize>,
    default: Option<TokenStream>,
    into: Option<TokenStream>,
    from: Option<TokenStream>,
}

impl Parse for BitsAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut attr = Self {
            bits: None,
            default: None,
            into: None,
            from: None,
        };
        if let Ok(bits) = syn::LitInt::parse(input) {
            attr.bits = Some(bits.base10_parse()?);
            if !input.is_empty() {
                <Token![,]>::parse(input)?;
            }
        }
        // parse remainder
        if !input.is_empty() {
            loop {
                let ident = syn::Ident::parse(input)?;

                <Token![=]>::parse(input)?;

                let expr = syn::Expr::parse(input)?.into_token_stream();

                if ident == "default" {
                    attr.default = Some(expr);
                } else if ident == "into" {
                    attr.into = Some(expr);
                } else if ident == "from" {
                    attr.from = Some(expr);
                }

                if input.is_empty() {
                    break;
                }

                <Token![,]>::parse(input)?;
            }
        }
        Ok(attr)
    }
}

/// Returns the number of bits for a given type
fn type_bits(ty: &syn::Type) -> (TypeClass, usize) {
    let syn::Type::Path(syn::TypePath{ path, .. }) = ty else {
        return (TypeClass::Other, 0);
    };
    let Some(ident) = path.get_ident() else {
        return (TypeClass::Other, 0);
    };
    if ident == "bool" {
        return (TypeClass::Bool, 1);
    }
    if ident == "isize" || ident == "usize" {
        return (TypeClass::UInt, 0); // they have architecture dependend sizes
    }
    macro_rules! integer {
        ($ident:ident => $($uint:ident),* ; $($sint:ident),*) => {
            match ident {
                $(_ if ident == stringify!($uint) => (TypeClass::UInt, $uint::BITS as _),)*
                $(_ if ident == stringify!($sint) => (TypeClass::SInt, $sint::BITS as _),)*
                _ => (TypeClass::Other, 0)
            }
        };
    }
    integer!(ident => u8, u16, u32, u64, u128 ; i8, i16, i32, i64, i128)
}

/// The bitfield macro parameters
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
        let (class, bits) = type_bits(&ty);
        if class != TypeClass::UInt {
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

#[cfg(test)]
mod test {
    use quote::quote;

    use crate::{BitsAttr, Params};

    #[test]
    fn parse_args() {
        let args = quote!(u64);
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bits == u64::BITS as usize && params.debug == true);

        let args = quote!(u32, debug = false);
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bits == u32::BITS as usize && params.debug == false);
    }

    #[test]
    fn parse_bits() {
        let args = quote!(8);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(8));
        assert!(attr.default.is_none());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());

        let args = quote!(8, default = 8);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(8));
        assert!(attr.default.is_some());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());

        let args = quote!(default = 8);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, None);
        assert!(attr.default.is_some());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());

        let args = quote!(3, into = this as _, default = 1, from = this as _);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(3));
        assert!(attr.default.is_some());
        assert!(attr.into.is_some());
        assert!(attr.from.is_some());
    }
}

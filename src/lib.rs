//! # Bitfield Struct
//!
//! Procedural macro for bitfields that allows specifying bitfields as structs.
//! As this library provides a procedural-macro it has no runtime dependencies and works for `no-std`.
//!
//! ## Example
//!
//! ```
//! use bitfield_struct::bitfield;
//!
//! #[bitfield(u64)]
//! #[derive(Default, PartialEq, Eq)] // Attributes are also applied
//! struct PageTableEntry {
//!     /// defaults to 32 bits for u32
//!     addr: u32,
//!
//!     /// public field -> public accessor functions
//!     #[bits(12)]
//!     pub size: usize,
//!
//!     /// padding: No accessor functions are generated for fields beginning with `_`.
//!     #[bits(6)]
//!     _p: u8,
//!
//!     /// interpreted as 1 bit flag
//!     present: bool,
//!
//!     /// sign extend for signed integers
//!     #[bits(13)]
//!     negative: i16,
//! }
//! ```
//!
//! The macro generates three accessor functions for each field.
//! Each accessor also inherits the documentation of its field.
//!
//! The signatures for `addr` are:
//!
//! ```ignore
//! // generated struct
//! struct PageTableEntry(u64);
//! impl PageTableEntry {
//!     const fn new() -> Self { Self(0) }
//!
//!     const ADDR_BITS: usize = 32;
//!     const ADDR_OFFSET: usize = 0;
//!
//!     const fn with_addr(self, value: u32) -> Self { /* ... */ }
//!     const fn addr(&self) -> u32 { /* ... */ }
//!     fn set_addr(&mut self, value: u32) { /* ... */ }
//!
//!     // other field ...
//! }
//! // generated trait implementations
//! impl From<u64> for PageTableEntry { /* ... */ }
//! impl From<PageTableEntry> for u64 { /* ... */ }
//! impl Debug for PageTableEntry { /* ... */ }
//! ```
//!
//! This generated bitfield can then be used as follows.
//!
//! ```
//! # use bitfield_struct::bitfield;
//! #
//! # #[bitfield(u64)]
//! # struct PageTableEntry {
//! #     addr: u32,
//! #     #[bits(12)]
//! #     pub size: usize,
//! #     #[bits(6)]
//! #     _p: u8,
//! #     present: bool,
//! #     #[bits(13)]
//! #     negative: i16,
//! # }
//!
//! let mut pte = PageTableEntry::new()
//!     .with_addr(3 << 31)
//!     .with_size(2)
//!     .with_present(false)
//!     .with_negative(-3);
//!
//! println!("{pte:?}");
//! assert!(pte.addr() == 3 << 31);
//!
//! pte.set_size(1);
//!
//! let value: u64 = pte.into();
//! println!("{value:b}");
//! ```
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
//! ```
//!

use proc_macro as pc;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{AttrStyle, Attribute, LitBool, LitInt, Token, Type};

/// Creates a bitfield for this struct.
///
/// The arguments first, have to begin with the underlying type of the bitfield:
/// For example: `#[bitfield(u64)]`.
///
/// Then optionally can contain an extra debug argument, for disabling the automatic Debug trait generation.
/// Like: `#[bitfield(u64, debug = false)]`
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
    let mut members = TokenStream::new();
    let mut debug_fields = TokenStream::new();

    for field in fields.named {
        if let Some((name, tokens)) = bitfield_member(field, &ty, &mut offset)? {
            members.extend(tokens);
            let name_str = name.to_string();
            debug_fields.extend(quote!(.field(#name_str, &self.#name())));
        }
    }

    if offset != bits {
        return Err(syn::Error::new(
            span,
            format!(
                "The bitfiled size has to be equal to the sum of its members! {bits} != {offset}. \
                Padding can be done by prefixing members with \"_\" which are ignored."
            ),
        ));
    }

    let debug_impl = if debug {
        quote! {
            impl core::fmt::Debug for #name {
                fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                    f.debug_struct(#name_str)
                        #debug_fields
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

            #members
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

fn bitfield_member(
    f: syn::Field,
    base_ty: &Type,
    offset: &mut usize,
) -> syn::Result<Option<(Ident, TokenStream)>> {
    let syn::Field {
        ty,
        vis,
        ident,
        attrs,
        ..
    } = &f;

    let bits = bits(attrs, ty)?;
    if bits == 0 {
        // Skip zero sized types
        return Ok(None);
    }

    let start = *offset;
    *offset = start + bits;

    let Some(name) = ident
        .as_ref()
        .and_then(|name| (!name.to_string().starts_with('_')).then_some(name)) else {
        // Skip if unnamed
        return Ok(None);
    };

    let with_name = format_ident!("with_{name}");
    let set_name = format_ident!("set_{name}");
    let bits_name = format_ident!("{}_BITS", name.to_string().to_uppercase());
    let offset_name = format_ident!("{}_OFFSET", name.to_string().to_uppercase());

    let location = format!("\n\nBits: {start}..{offset}");

    let doc: TokenStream = attrs
        .iter()
        .filter(|a| !a.path.is_ident("bits"))
        .map(ToTokens::to_token_stream)
        .collect();

    if bits > 1 {
        let mask: u128 = !0 >> (u128::BITS as usize - bits);
        let mask = LitInt::new(&format!("0x{mask:x}"), Span::mixed_site());

        Ok(Some((
            name.clone(),
            quote! {
                const #bits_name: usize = #bits;
                const #offset_name: usize = #start;

                #doc
                #[doc = #location]
                #vis const fn #with_name(self, value: #ty) -> Self {
                    debug_assert!(value <= #mask);
                    Self(self.0 & !(#mask << #start) | (value as #base_ty & #mask) << #start)
                }
                #doc
                #[doc = #location]
                #vis const fn #name(&self) -> #ty {
                    (((self.0 >> #start) as #ty) << #ty::BITS as usize - #bits) >> #ty::BITS as usize - #bits
                }
                #doc
                #[doc = #location]
                #vis fn #set_name(&mut self, value: #ty) {
                    debug_assert!(value <= #mask);
                    *self = self.#with_name(value);
                }
            },
        )))
    } else {
        // Casting to a bool or a number is syntactically different...
        let cast = if matches!(ty, Type::Path(p) if p.path.is_ident("bool")) {
            quote! { != 0 }
        } else {
            quote! { as _ }
        };

        Ok(Some((
            name.clone(),
            quote! {
                const #bits_name: usize = #bits;
                const #offset_name: usize = #start;

                #doc
                #[doc = #location]
                #vis const fn #with_name(self, value: #ty) -> Self {
                    Self(self.0 & !(1 << #start) | (value as #base_ty & 1) << #start)
                }
                #doc
                #[doc = #location]
                #vis const fn #name(&self) -> #ty {
                    ((self.0 >> #start) & 1) #cast
                }
                #doc
                #[doc = #location]
                #vis fn #set_name(&mut self, value: #ty) {
                    *self = self.#with_name(value);
                }
            },
        )))
    }
}

/// Parses the `bits` attribute that allows specifying a custom number of bits.
fn bits(attrs: &[Attribute], ty: &Type) -> syn::Result<usize> {
    fn malformed(mut e: syn::Error, attr: &Attribute) -> syn::Error {
        e.combine(syn::Error::new_spanned(attr, "malformed #[bits] attribute"));
        e
    }

    for attr in attrs {
        match attr {
            Attribute {
                style: AttrStyle::Outer,
                path,
                tokens,
                ..
            } if path.is_ident("bits") => {
                let bits = attr
                    .parse_args::<LitInt>()
                    .map_err(|e| malformed(e, attr))?
                    .base10_parse()
                    .map_err(|e| malformed(e, attr))?;

                return if bits == 0 {
                    Ok(0)
                } else if bits <= type_bits(ty)? {
                    Ok(bits)
                } else {
                    Err(syn::Error::new_spanned(&tokens, "overflowing member type"))
                };
            }
            _ => {}
        }
    }

    // Fallback to type size
    type_bits(ty)
}

/// Returns the number of bits for a given type
fn type_bits(ty: &Type) -> syn::Result<usize> {
    match ty {
        Type::Path(path) if path.path.is_ident("bool") => Ok(1),
        Type::Path(path) if path.path.is_ident("u8") => Ok(u8::BITS as _),
        Type::Path(path) if path.path.is_ident("i8") => Ok(i8::BITS as _),
        Type::Path(path) if path.path.is_ident("u16") => Ok(u16::BITS as _),
        Type::Path(path) if path.path.is_ident("i16") => Ok(i16::BITS as _),
        Type::Path(path) if path.path.is_ident("u32") => Ok(u32::BITS as _),
        Type::Path(path) if path.path.is_ident("i32") => Ok(i32::BITS as _),
        Type::Path(path) if path.path.is_ident("u64") => Ok(u64::BITS as _),
        Type::Path(path) if path.path.is_ident("i64") => Ok(i64::BITS as _),
        Type::Path(path) if path.path.is_ident("u128") => Ok(u128::BITS as _),
        Type::Path(path) if path.path.is_ident("i128") => Ok(i128::BITS as _),
        Type::Path(path) if path.path.is_ident("usize") => Ok(usize::BITS as _),
        Type::Path(path) if path.path.is_ident("isize") => Ok(isize::BITS as _),
        _ => Err(syn::Error::new_spanned(ty, "unsupported type")),
    }
}

struct Params {
    ty: Type,
    bits: usize,
    debug: bool,
}

impl Parse for Params {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let Ok(ty) = Type::parse(input) else {
            return Err(syn::Error::new(input.span(), "unknown type"));
        };
        let bits = type_bits(&ty)?;

        // try parse additional debug arg
        let debug = if <Token![,]>::parse(input).is_ok() {
            let ident = Ident::parse(input)?;

            if ident != "debug" {
                return Err(syn::Error::new(ident.span(), "unknown argument"));
            }
            <Token![=]>::parse(input)?;

            let val = LitBool::parse(input)?;
            val.value
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

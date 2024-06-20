// Generate docs from readme
#![doc = include_str!("../README.md")]
#![warn(clippy::unwrap_used)]

use proc_macro as pc;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::{fmt, stringify};
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::Token;

fn s_err(span: proc_macro2::Span, msg: impl fmt::Display) -> syn::Error {
    syn::Error::new(span, msg)
}

/// Creates a bitfield for this struct.
///
/// The arguments first, have to begin with the integer type of the bitfield:
/// For example: `#[bitfield(u64)]`.
///
/// It can contain the following additional parameters, like the `debug` argument
/// for disabling the `Debug` trait generation (`#[bitfield(u64, debug = false)]`).
///
/// Parameters of the `bitfield` attribute:
/// - the bitfield integer type (required)
/// - `repr` specifies the bitfield's representation in memory
/// - `from` to specify a conversion function from repr to the bitfield's integer type
/// - `into` to specify a conversion function from the bitfield's integer type to repr
/// - `debug` to disable the `Debug` trait generation
/// - `defmt` to enable the `defmt::Format` trait generation.
/// - `default` to disable the `Default` trait generation
/// - `order` to specify the bit order (Lsb, Msb)
/// - `conversion` to disable the generation of into_bits and from_bits
///
/// Parameters of the `bits` attribute (for fields):
/// - the number of bits
/// - `access` to specify the access mode (RW, RO, WO, None)
/// - `default` to set a default value
/// - `into` to specify a conversion function from the field type to the bitfield type
/// - `from` to specify a conversion function from the bitfield type to the field type
#[proc_macro_attribute]
pub fn bitfield(args: pc::TokenStream, input: pc::TokenStream) -> pc::TokenStream {
    match bitfield_inner(args.into(), input.into()) {
        Ok(result) => result.into(),
        Err(e) => e.into_compile_error().into(),
    }
}

fn bitfield_inner(args: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    let input = syn::parse2::<syn::ItemStruct>(input)?;
    let Params {
        ty,
        repr,
        into,
        from,
        bits,
        debug,
        defmt,
        default,
        order,
        conversion,
    } = syn::parse2(args)?;

    let span = input.fields.span();
    let name = input.ident;
    let vis = input.vis;
    let attrs: TokenStream = input.attrs.iter().map(ToTokens::to_token_stream).collect();

    let syn::Fields::Named(fields) = input.fields else {
        return Err(s_err(span, "only named fields are supported"));
    };

    let mut offset = 0;
    let mut members = Vec::with_capacity(fields.named.len());
    for field in fields.named {
        let f = Member::new(
            ty.clone(),
            bits,
            into.clone(),
            from.clone(),
            field,
            offset,
            order,
        )?;
        offset += f.bits;
        members.push(f);
    }

    if offset < bits {
        return Err(s_err(
            span,
            format!(
                "The bitfield size ({bits} bits) has to be equal to the sum of its members ({offset} bits)!. \
                You might have to add padding (a {} bits large member prefixed with \"_\").",
                bits - offset
            ),
        ));
    }
    if offset > bits {
        return Err(s_err(
            span,
            format!(
                "The size of the members ({offset} bits) is larger than the type ({bits} bits)!."
            ),
        ));
    }

    let mut impl_debug = TokenStream::new();
    if let Some(cfg) = debug.cfg() {
        impl_debug.extend(implement_debug(&name, &members, cfg));
    }
    if let Some(cfg) = defmt.cfg() {
        impl_debug.extend(implement_defmt(&name, &members, cfg));
    }

    let defaults = members.iter().map(Member::default);

    let impl_default = default.cfg().map(|cfg| {
        let attr = cfg.map(|cfg| quote!(#[cfg(#cfg)]));
        quote! {
            #attr
            impl Default for #name {
                fn default() -> Self {
                    Self::new()
                }
            }
        }
    });

    let conversion = conversion.then(|| {
        quote! {
            /// Convert from bits.
            #vis const fn from_bits(bits: #repr) -> Self {
                Self(bits)
            }
            /// Convert into bits.
            #vis const fn into_bits(self) -> #repr {
                self.0
            }
        }
    });

    Ok(quote! {
        #attrs
        #[derive(Copy, Clone)]
        #[repr(transparent)]
        #vis struct #name(#repr);

        impl #name {
            /// Creates a new default initialized bitfield.
            #vis const fn new() -> Self {
                let mut this = Self(#from(0));
                #( #defaults )*
                this
            }
            #conversion

            #( #members )*
        }

        #impl_default

        impl From<#repr> for #name {
            fn from(v: #repr) -> Self {
                Self(v)
            }
        }
        impl From<#name> for #repr {
            fn from(v: #name) -> #repr {
                v.0
            }
        }

        #impl_debug
    })
}

fn implement_debug(name: &syn::Ident, members: &[Member], cfg: Option<TokenStream>) -> TokenStream {
    let fields = members.iter().flat_map(|m| {
        let inner = m.inner.as_ref()?;
        if inner.from.is_empty() {
            return None;
        }

        let ident = &inner.ident;
        Some(quote!(.field(stringify!(#ident), &self.#ident())))
    });

    let attr = cfg.map(|cfg| quote!(#[cfg(#cfg)]));

    quote! {
        #attr
        impl core::fmt::Debug for #name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_struct(stringify!(#name))
                    #( #fields )*
                    .finish()
            }
        }
    }
}

fn implement_defmt(name: &syn::Ident, members: &[Member], cfg: Option<TokenStream>) -> TokenStream {
    // build a part of the format string for each field
    let formats = members.iter().flat_map(|m| {
        let inner = m.inner.as_ref()?;
        if inner.from.is_empty() {
            return None;
        }

        // primitives supported by defmt
        const PRIMITIVES: &[&str] = &[
            "bool", "usize", "isize", //
            "u8", "u16", "u32", "u64", "u128", //
            "i8", "i16", "i32", "i64", "i128", //
            "f32", "f64", //
        ];

        // get the type name so we can use more efficient defmt formats
        // if it's a primitive
        if let syn::Type::Path(syn::TypePath { path, .. }) = &inner.ty {
            if let Some(ident) = path.get_ident() {
                if PRIMITIVES.iter().any(|s| ident == s) {
                    // defmt supports this primitive, use special spec
                    return Some(format!("{}: {{={ident}}}", inner.ident));
                }
            }
        }

        Some(format!("{}: {{:?}}", inner.ident))
    });

    // find the corresponding format argument for each field
    let args = members.iter().flat_map(|m| {
        let inner = m.inner.as_ref()?;
        if inner.from.is_empty() {
            return None;
        }

        let ident = &inner.ident;
        Some(quote!(self.#ident()))
    });

    // build a string like "Foo { field_name: {:?}, ... }"
    // four braces, two to escape *this* format, times two to escape
    // the defmt::write! call below.
    let format_string = format!(
        "{name} {{{{ {} }}}} ",
        formats.collect::<Vec<_>>().join(", ")
    );

    let attr = cfg.map(|cfg| quote!(#[cfg(#cfg)]));

    // note: we use defmt paths here, not ::defmt, because many crates
    // in the embedded space will rename defmt (e.g. to defmt_03) in
    // order to support multiple incompatible defmt versions.
    //
    // defmt itself avoids ::defmt for this reason. For more info, see:
    // https://github.com/knurling-rs/defmt/pull/835
    quote! {
        #attr
        impl defmt::Format for #name {
            fn format(&self, f: defmt::Formatter) {
                defmt::write!(f, #format_string, #( #args, )*)
            }
        }
    }
}

/// Represents a member where accessor functions should be generated for.
struct Member {
    offset: usize,
    bits: usize,
    base_ty: syn::Type,
    repr_into: Option<syn::Path>,
    repr_from: Option<syn::Path>,
    default: TokenStream,
    inner: Option<MemberInner>,
}

struct MemberInner {
    ident: syn::Ident,
    ty: syn::Type,
    attrs: Vec<syn::Attribute>,
    vis: syn::Visibility,
    into: TokenStream,
    from: TokenStream,
}

impl Member {
    fn new(
        base_ty: syn::Type,
        base_bits: usize,
        repr_into: Option<syn::Path>,
        repr_from: Option<syn::Path>,
        f: syn::Field,
        offset: usize,
        order: Order,
    ) -> syn::Result<Self> {
        let span = f.span();

        let syn::Field {
            mut attrs,
            vis,
            ident,
            ty,
            ..
        } = f;

        let ident = ident.ok_or_else(|| s_err(span, "Not supported"))?;
        let ignore = ident.to_string().starts_with('_');

        let Field {
            bits,
            ty,
            mut default,
            into,
            from,
            access,
        } = parse_field(&base_ty, &attrs, &ty, ignore)?;

        let ignore = ignore || access == Access::None;

        if bits > 0 && !ignore {
            // overflow check
            if offset + bits > base_bits {
                return Err(s_err(
                    ty.span(),
                    "The sum of the members overflows the type size",
                ));
            };

            // clear conversion expr if not needed
            let (from, into) = match access {
                Access::ReadWrite => (from, into),
                Access::ReadOnly => (from, quote!()),
                Access::WriteOnly => (quote!(), into),
                Access::None => (quote!(), quote!()),
            };

            // compute the offset
            let offset = if order == Order::Lsb {
                offset
            } else {
                base_bits - offset - bits
            };

            // auto-conversion from zero
            if default.is_empty() {
                if !from.is_empty() {
                    default = quote!({ let this = 0; #from });
                } else {
                    default = quote!(0);
                }
            }

            // remove our attribute
            attrs.retain(|a| !a.path().is_ident("bits"));

            Ok(Self {
                offset,
                bits,
                base_ty,
                repr_into,
                repr_from,
                default,
                inner: Some(MemberInner {
                    ident,
                    ty,
                    attrs,
                    vis,
                    into,
                    from,
                }),
            })
        } else {
            if default.is_empty() {
                default = quote!(0);
            }

            Ok(Self {
                offset,
                bits,
                base_ty,
                repr_into,
                repr_from,
                default,
                inner: None,
            })
        }
    }

    fn default(&self) -> TokenStream {
        let default = &self.default;

        if let Some(inner) = &self.inner {
            if !inner.into.is_empty() {
                let ident = &inner.ident;
                let with_ident = format_ident!("with_{}", ident);
                return quote!(this = this.#with_ident(#default););
            }
        }
        let offset = self.offset;
        let base_ty = &self.base_ty;
        quote!(this.0 |= (#default as #base_ty) << #offset;)
    }
}

impl ToTokens for Member {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Self {
            offset,
            bits,
            base_ty,
            repr_into,
            repr_from,
            default: _,
            inner:
                Some(MemberInner {
                    ident,
                    ty,
                    attrs,
                    vis,
                    into,
                    from,
                }),
        } = self
        else {
            return Default::default();
        };

        let ident_str = ident.to_string().to_uppercase();
        let ident_upper = Ident::new(
            ident_str.strip_prefix("R#").unwrap_or(&ident_str),
            ident.span(),
        );

        let with_ident = format_ident!("with_{}", ident);
        let set_ident = format_ident!("set_{}", ident);
        let bits_ident = format_ident!("{}_BITS", ident_upper);
        let offset_ident = format_ident!("{}_OFFSET", ident_upper);

        let location = format!("\n\nBits: {offset}..{}", offset + bits);

        let doc: TokenStream = attrs
            .iter()
            .filter(|a| !a.path().is_ident("bits"))
            .map(ToTokens::to_token_stream)
            .collect();

        tokens.extend(quote! {
            const #bits_ident: usize = #bits;
            const #offset_ident: usize = #offset;
        });

        if !from.is_empty() {
            tokens.extend(quote! {
                #doc
                #[doc = #location]
                #vis const fn #ident(&self) -> #ty {
                    let mask = #base_ty::MAX >> (#base_ty::BITS - Self::#bits_ident as u32);
                    let this = (#repr_into(self.0) >> Self::#offset_ident) & mask;
                    #from
                }
            });
        }

        if !into.is_empty() {
            tokens.extend(quote! {
                #doc
                #[doc = #location]
                #[cfg_attr(debug_assertions, track_caller)]
                #vis const fn #with_ident(self, value: #ty) -> Self {
                    let this = value;
                    let value: #base_ty = #into;
                    let mask = #base_ty::MAX >> (#base_ty::BITS - Self::#bits_ident as u32);
                    #[allow(unused_comparisons)]
                    debug_assert!(value <= mask, "value out of bounds");
                    let bits = #repr_into(self.0) & !(mask << Self::#offset_ident) | (value & mask) << Self::#offset_ident;
                    Self(#repr_from(bits))
                }

                #doc
                #[doc = #location]
                #[cfg_attr(debug_assertions, track_caller)]
                #vis fn #set_ident(&mut self, value: #ty) {
                    *self = self.#with_ident(value);
                }
            });
        }
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

    default: TokenStream,
    into: TokenStream,
    from: TokenStream,

    access: Access,
}

/// Parses the `bits` attribute that allows specifying a custom number of bits.
fn parse_field(
    base_ty: &syn::Type,
    attrs: &[syn::Attribute],
    ty: &syn::Type,
    ignore: bool,
) -> syn::Result<Field> {
    fn malformed(mut e: syn::Error, attr: &syn::Attribute) -> syn::Error {
        e.combine(s_err(attr.span(), "malformed #[bits] attribute"));
        e
    }

    let access = if ignore {
        Access::None
    } else {
        Access::ReadWrite
    };

    // Defaults for the different types
    let (class, ty_bits) = type_bits(ty);
    let mut ret = match class {
        TypeClass::Bool => Field {
            bits: ty_bits,
            ty: ty.clone(),
            default: quote!(false),
            into: quote!(this as _),
            from: quote!(this != 0),
            access,
        },
        TypeClass::SInt => Field {
            bits: ty_bits,
            ty: ty.clone(),
            default: quote!(0),
            into: quote!(),
            from: quote!(),
            access,
        },
        TypeClass::UInt => Field {
            bits: ty_bits,
            ty: ty.clone(),
            default: quote!(0),
            into: quote!(this as _),
            from: quote!(this as _),
            access,
        },
        TypeClass::Other => Field {
            bits: ty_bits,
            ty: ty.clone(),
            default: quote!(),
            into: quote!(<#ty>::into_bits(this) as _),
            from: quote!(<#ty>::from_bits(this as _)),
            access,
        },
    };

    // Find and parse the bits attribute
    for attr in attrs {
        let syn::Attribute {
            style: syn::AttrStyle::Outer,
            meta: syn::Meta::List(syn::MetaList { path, tokens, .. }),
            ..
        } = attr
        else {
            continue;
        };
        if !path.is_ident("bits") {
            continue;
        }

        let span = tokens.span();
        let BitsAttr {
            bits,
            default,
            into,
            from,
            access,
        } = syn::parse2(tokens.clone()).map_err(|e| malformed(e, attr))?;

        // bit size
        if let Some(bits) = bits {
            if bits == 0 {
                return Err(s_err(span, "bits cannot bit 0"));
            }
            if ty_bits != 0 && bits > ty_bits {
                return Err(s_err(span, "overflowing field type"));
            }
            ret.bits = bits;
        }

        // read/write access
        if let Some(access) = access {
            if ignore {
                return Err(s_err(
                    tokens.span(),
                    "'access' is not supported for padding",
                ));
            }
            ret.access = access;
        }

        // conversion
        if let Some(into) = into {
            if ret.access == Access::None {
                return Err(s_err(into.span(), "'into' is not supported on padding"));
            }
            ret.into = quote!(#into(this) as _);
        }
        if let Some(from) = from {
            if ret.access == Access::None {
                return Err(s_err(from.span(), "'from' is not supported on padding"));
            }
            ret.from = quote!(#from(this as _));
        }
        if let Some(default) = default {
            ret.default = default.into_token_stream();
        }
    }

    if ret.bits == 0 {
        return Err(s_err(
            ty.span(),
            "Custom types and isize/usize require an explicit bit size",
        ));
    }

    // Signed integers need some special handling...
    if !ignore && ret.access != Access::None && class == TypeClass::SInt {
        let bits = ret.bits as u32;
        if ret.into.is_empty() {
            // Bounds check and remove leading ones from negative values
            ret.into = quote! {{
                debug_assert!({
                    let m = #ty::MIN >> (#ty::BITS - #bits);
                    m <= this && this <= -(m + 1)
                });
                let mask = #base_ty::MAX >> (#base_ty::BITS - #bits);
                (this as #base_ty & mask)
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
    default: Option<syn::Expr>,
    into: Option<syn::Path>,
    from: Option<syn::Path>,
    access: Option<Access>,
}

impl Parse for BitsAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut attr = Self {
            bits: None,
            default: None,
            into: None,
            from: None,
            access: None,
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

                if ident == "default" {
                    attr.default = Some(input.parse()?);
                } else if ident == "into" {
                    attr.into = Some(input.parse()?);
                } else if ident == "from" {
                    attr.from = Some(input.parse()?);
                } else if ident == "access" {
                    attr.access = Some(input.parse()?);
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Access {
    ReadWrite,
    ReadOnly,
    WriteOnly,
    None,
}

impl Parse for Access {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mode = input.parse::<Ident>()?;

        if mode == "RW" {
            Ok(Self::ReadWrite)
        } else if mode == "RO" {
            Ok(Self::ReadOnly)
        } else if mode == "WO" {
            Ok(Self::WriteOnly)
        } else if mode == "None" {
            Ok(Self::None)
        } else {
            Err(s_err(
                mode.span(),
                "Invalid access mode, only RW, RO, WO, or None are allowed",
            ))
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Order {
    Lsb,
    Msb,
}

#[derive(Debug, Clone)]
enum Enable {
    No,
    Yes,
    Cfg(TokenStream),
}
impl Enable {
    fn cfg(self) -> Option<Option<TokenStream>> {
        match self {
            Enable::No => None,
            Enable::Yes => Some(None),
            Enable::Cfg(c) => Some(Some(c)),
        }
    }
}
impl Parse for Enable {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(if let Ok(lit_bool) = syn::LitBool::parse(input) {
            if lit_bool.value {
                Enable::Yes
            } else {
                Enable::No
            }
        } else {
            let meta = syn::MetaList::parse(input)?;
            if matches!(meta.delimiter, syn::MacroDelimiter::Paren(_)) && meta.path.is_ident("cfg")
            {
                Enable::Cfg(meta.tokens)
            } else {
                return Err(s_err(meta.span(), "Only `cfg` attributes are allowed"));
            }
        })
    }
}

/// The bitfield macro parameters
struct Params {
    ty: syn::Type,
    repr: syn::Type,
    into: Option<syn::Path>,
    from: Option<syn::Path>,
    bits: usize,
    debug: Enable,
    defmt: Enable,
    default: Enable,
    order: Order,
    conversion: bool,
}

impl Parse for Params {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let Ok(ty) = syn::Type::parse(input) else {
            return Err(s_err(input.span(), "unknown type"));
        };
        let (class, bits) = type_bits(&ty);
        if class != TypeClass::UInt {
            return Err(s_err(input.span(), "unsupported type"));
        }

        let mut ret = Params {
            repr: ty.clone(),
            ty,
            into: None,
            from: None,
            bits,
            debug: Enable::Yes,
            defmt: Enable::No,
            default: Enable::Yes,
            order: Order::Lsb,
            conversion: true,
        };

        // try parse additional args
        while <Token![,]>::parse(input).is_ok() {
            let ident = Ident::parse(input)?;
            <Token![=]>::parse(input)?;
            match ident.to_string().as_str() {
                "repr" => {
                    ret.repr = input.parse()?;
                }
                "from" => {
                    ret.from = Some(input.parse()?);
                }
                "into" => {
                    ret.into = Some(input.parse()?);
                }
                "debug" => {
                    ret.debug = input.parse()?;
                }
                "defmt" => {
                    ret.defmt = input.parse()?;
                }
                "default" => {
                    ret.default = input.parse()?;
                }
                "order" => {
                    ret.order = match syn::Ident::parse(input)?.to_string().as_str() {
                        "Msb" | "msb" => Order::Msb,
                        "Lsb" | "lsb" => Order::Lsb,
                        _ => return Err(s_err(ident.span(), "unknown value for order")),
                    };
                }
                "conversion" => {
                    ret.conversion = syn::LitBool::parse(input)?.value;
                }
                _ => return Err(s_err(ident.span(), "unknown argument")),
            };
        }

        if ret.repr != ret.ty && (ret.from.is_none() || ret.into.is_none()) {
            return Err(s_err(
                input.span(),
                "`repr` requires both `from` and `into`",
            ));
        }

        Ok(ret)
    }
}

/// Returns the number of bits for a given type
fn type_bits(ty: &syn::Type) -> (TypeClass, usize) {
    let syn::Type::Path(syn::TypePath { path, .. }) = ty else {
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

#[cfg(test)]
mod test {
    use quote::quote;

    use crate::{Access, BitsAttr, Enable, Order, Params};

    #[test]
    fn parse_args() {
        let args = quote!(u64);
        let params = syn::parse2::<Params>(args).unwrap();
        assert_eq!(params.bits, u64::BITS as usize);
        assert!(matches!(params.debug, Enable::Yes));
        assert!(matches!(params.defmt, Enable::No));

        let args = quote!(u32, debug = false);
        let params = syn::parse2::<Params>(args).unwrap();
        assert_eq!(params.bits, u32::BITS as usize);
        assert!(matches!(params.debug, Enable::No));
        assert!(matches!(params.defmt, Enable::No));

        let args = quote!(u32, defmt = true);
        let params = syn::parse2::<Params>(args).unwrap();
        assert_eq!(params.bits, u32::BITS as usize);
        assert!(matches!(params.debug, Enable::Yes));
        assert!(matches!(params.defmt, Enable::Yes));

        let args = quote!(u32, defmt = cfg(test), debug = cfg(feature = "foo"));
        let params = syn::parse2::<Params>(args).unwrap();
        assert_eq!(params.bits, u32::BITS as usize);
        assert!(matches!(params.debug, Enable::Cfg(_)));
        assert!(matches!(params.defmt, Enable::Cfg(_)));

        let args = quote!(u32, order = Msb);
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bits == u32::BITS as usize && params.order == Order::Msb);
    }

    #[test]
    fn parse_bits() {
        let args = quote!(8);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(8));
        assert!(attr.default.is_none());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());
        assert!(attr.access.is_none());

        let args = quote!(8, default = 8, access = RW);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(8));
        assert!(attr.default.is_some());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());
        assert_eq!(attr.access, Some(Access::ReadWrite));

        let args = quote!(access = RO);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, None);
        assert!(attr.default.is_none());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());
        assert_eq!(attr.access, Some(Access::ReadOnly));

        let args = quote!(default = 8, access = WO);
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, None);
        assert!(attr.default.is_some());
        assert!(attr.into.is_none());
        assert!(attr.from.is_none());
        assert_eq!(attr.access, Some(Access::WriteOnly));

        let args = quote!(
            3,
            into = into_something,
            default = 1,
            from = from_something,
            access = None
        );
        let attr = syn::parse2::<BitsAttr>(args).unwrap();
        assert_eq!(attr.bits, Some(3));
        assert!(attr.default.is_some());
        assert!(attr.into.is_some());
        assert!(attr.from.is_some());
        assert_eq!(attr.access, Some(Access::None));
    }

    #[test]
    fn parse_access_mode() {
        let args = quote!(RW);
        let mode = syn::parse2::<Access>(args).unwrap();
        assert_eq!(mode, Access::ReadWrite);

        let args = quote!(RO);
        let mode = syn::parse2::<Access>(args).unwrap();
        assert_eq!(mode, Access::ReadOnly);

        let args = quote!(WO);
        let mode = syn::parse2::<Access>(args).unwrap();
        assert_eq!(mode, Access::WriteOnly);

        let args = quote!(None);
        let mode = syn::parse2::<Access>(args).unwrap();
        assert_eq!(mode, Access::None);

        let args = quote!(garbage);
        let mode = syn::parse2::<Access>(args);
        assert!(mode.is_err());
    }
}

use proc_macro as pc;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::stringify;
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::Token;

/// Creates a bitfield for this struct.
///
/// There are two ways to specify the size and alignment of the bitfield:
///
/// - Integer type: `#[bitfield(u32)]`
///   - All explicitly sized integers are supported
///   - The alignment defaults to the alignment of the integer if not otherwise specified
/// - Bytes argument: `#[bitfield(bytes = 3)]`
///   - The default alignment is 1
///
/// The macro two optional arguments
/// - `align`: Specifies the alignment of the bitfield
/// - `debug`: Whether or not the fmt::Debug trait should be generated (default: true)
///
/// For example: `#[bitfield(bytes = 6, align = 2, debug = false)]`
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
        bytes,
        align,
        debug,
        ty,
    } = syn::parse2::<Params>(args)?;

    let bits = bytes * 8;
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
        let f = Member::new(field, offset)?;
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

    // The size of isize and usize is architecture dependent and not known for proc_macros,
    // thus we have to check it with const asserts.
    let const_asserts = members.iter().filter_map(|m| {
        if m.class == TypeClass::SizeInt {
            let bits = m.bits;
            let msg = format!("overflowing field type of '{}'", m.ident);
            Some(quote!(
                const _: () = assert!(#bits <= 8 * std::mem::size_of::<usize>(), #msg);
            ))
        } else {
            None
        }
    });
    let type_conversion = if let Some(ty) = ty {
        Some(quote! {
            impl From<#ty> for #name {
                fn from(v: #ty) -> Self {
                    Self(v.to_be_bytes())
                }
            }
            impl From<#name> for #ty {
                fn from(v: #name) -> #ty {
                    #ty::from_be_bytes(v.0)
                }
            }
        })
    } else {
        None
    };

    let align = syn::LitInt::new(&format!("{align}"), Span::mixed_site());
    Ok(quote! {
        #attrs
        #[derive(Copy, Clone)]
        #[repr(align(#align))]
        #vis struct #name([u8; #bytes]);

        impl #name {
            #vis const fn new() -> Self {
                Self([0; #bytes])
            }

            #( #members )*
        }

        impl From<[u8; #bytes]> for #name {
            fn from(v: [u8; #bytes]) -> Self {
                Self(v)
            }
        }
        impl From<#name> for [u8; #bytes] {
            fn from(v: #name) -> [u8; #bytes] {
                v.0
            }
        }
        #type_conversion

        #( #const_asserts )*

        #debug_impl
    })
}

/// Distinguish between different types for code generation.
///
/// We need this to make accessor functions for bool and ints const.
/// As soon as we have const conversion traits, we can simply switch to `TryFrom` and don't have to generate different code.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum TypeClass {
    /// Booleans with 1 bit size
    Bool,
    /// Ints with fixes sizes: u8, u64, ...
    Int,
    /// Ints with architecture dependend sizes: usize, isize
    SizeInt,
    /// Custom types
    Other,
}

struct Member {
    attrs: Vec<syn::Attribute>,
    ty: syn::Type,
    class: TypeClass,
    bits: usize,
    ident: syn::Ident,
    vis: syn::Visibility,
    offset: usize,
}

impl Member {
    fn new(f: syn::Field, offset: usize) -> syn::Result<Self> {
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

        let bytes = (bits + 7) / 8;

        let code = match class {
            TypeClass::Bool => quote! {
                #general

                #doc
                #[doc = #location]
                #vis const fn #with_ident(self, value: #ty) -> Self {
                    let src = [value as u8];
                    Self(bitfield_struct::bit_copy(self.0, #offset, &src, 0, 1))
                }
                #doc
                #[doc = #location]
                #vis const fn #ident(&self) -> #ty {
                    bitfield_struct::is_bit_set(&self.0, #offset)
                }
            },
            TypeClass::Int | TypeClass::SizeInt => quote! {
                #general

                #doc
                #[doc = #location]
                #vis const fn #with_ident(self, value: #ty) -> Self {
                    #[cfg(target_endian = "little")]
                    let src = value.to_le_bytes();
                    #[cfg(target_endian = "big")]
                    let src = value.to_be_bytes();
                    Self(bitfield_struct::bit_copy(self.0, #offset, &src, 0, #bits))
                }
                #doc
                #[doc = #location]
                #vis const fn #ident(&self) -> #ty {
                    let out = bitfield_struct::bit_copy(
                        [0; #ty::BITS as usize / 8], #ty::BITS as usize - #bits, &self.0, #offset, #bits);
                    #[cfg(target_endian = "little")]
                    let out = #ty::from_le_bytes(out);
                    #[cfg(target_endian = "big")]
                    let out = #ty::from_be_bytes(out);
                    out >> (#ty::BITS as usize - #bits)
                }
            },
            TypeClass::Other => quote! {
                #general

                #doc
                #[doc = #location]
                #vis fn #with_ident(self, value: #ty) -> Self {
                    let src: [u8; #bytes] = value.into();
                    Self(bitfield_struct::bit_copy(self.0, #offset, &src, 0, #bits))
                }
                #doc
                #[doc = #location]
                #vis fn #ident(&self) -> #ty {
                    let out = bitfield_struct::bit_copy([0; #bytes], 0, &self.0, #offset, #bits);
                    out.into()
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
                } else if matches!(ty, syn::Type::Path(syn::TypePath{ path, .. })
                    if path.is_ident("usize") || path.is_ident("isize"))
                {
                    // isize and usize are supported but types size is not known at this point!
                    // Meaning that they must have a bits attribute explicitly defining their size
                    Ok((TypeClass::SizeInt, bits))
                } else {
                    Ok((TypeClass::Other, bits))
                };
            }
            _ => {}
        }
    }

    if let syn::Type::Path(syn::TypePath { path, .. }) = ty {
        if path.is_ident("usize") || path.is_ident("isize") {
            return Err(syn::Error::new(
                ty.span(),
                "isize and usize fields require the #[bits($1)] attribute",
            ));
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
    integer!(ident => u8, i8, u16, i16, u32, i32, u64, i64, u128, i128)
}

struct Params {
    ty: Option<syn::Type>,
    bytes: usize,
    align: usize,
    debug: bool,
}

impl Parse for Params {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut align = 1;
        let mut debug = true;
        let mut ty = None;

        let bytes = if input.peek2(Token![=]) && input.peek(syn::Ident) {
            Bytes::parse(input)?.bytes
        } else {
            let t = syn::Type::parse(input)?;
            let (class, bits) = type_bits(&t)?;
            if class != TypeClass::Int {
                return Err(syn::Error::new(
                    input.span(),
                    "Invalid argument or type, expecting `bytes` or an integer type",
                ));
            }
            ty = Some(t);
            align = bits / 8;
            bits / 8
        };

        if let Ok(_) = <Token![,]>::parse(input) {
            let params = Punctuated::<Param, Token![,]>::parse_terminated(input)?;
            for param in params {
                match param {
                    Param::Align(a) => align = a,
                    Param::Debug(d) => debug = d,
                }
            }
        }

        Ok(Params {
            ty,
            bytes,
            align,
            debug,
        })
    }
}

struct Bytes {
    bytes: usize,
}

impl Parse for Bytes {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident = Ident::parse(input)?;
        if ident != "bytes" {
            return Err(syn::Error::new(
                ident.span(),
                "Invalid argument, expecting `bytes` or an integer type",
            ));
        }
        <Token![=]>::parse(input)?;
        Ok(Self {
            bytes: syn::LitInt::parse(input)?.base10_parse()?,
        })
    }
}

enum Param {
    Align(usize),
    Debug(bool),
}

impl Parse for Param {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let ident = Ident::parse(input)?;

        <Token![=]>::parse(input)?;

        if ident == "align" {
            Ok(Self::Align(syn::LitInt::parse(input)?.base10_parse()?))
        } else if ident == "debug" {
            Ok(Self::Debug(syn::LitBool::parse(input)?.value))
        } else {
            Err(syn::Error::new(ident.span(), "unknown argument"))
        }
    }
}

#[cfg(test)]
mod test {
    use quote::quote;

    use crate::Params;

    #[test]
    fn parse_args() {
        let args = quote! {
            bytes = 3
        };
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bytes == 3 && params.debug == true);

        let args = quote! {
            bytes = 3, align = 2, debug = false
        };
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bytes == 3 && params.align == 2 && params.debug == false);

        let args = quote! {
            u64
        };
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bytes == 8 && params.debug == true);

        let args = quote! {
            u32, debug = false
        };
        let params = syn::parse2::<Params>(args).unwrap();
        assert!(params.bytes == 4 && params.debug == false);
    }
}

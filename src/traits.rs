use super::Member;
use proc_macro2::TokenStream;
use quote::quote;

/// Implements the `core::clone::Clone` trait for the given bitfield struct.
pub fn debug(
    name: &syn::Ident,
    members: &[Member],
    cfg: Option<TokenStream>,
) -> TokenStream {
    let fields = members.iter().filter_map(|m| {
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

/// Implements the `core::fmt::Display` trait for the given bitfield struct.
pub fn defmt(
    name: &syn::Ident,
    members: &[Member],
    cfg: Option<TokenStream>,
) -> TokenStream {
    // build a part of the format string for each field
    let formats = members.iter().filter_map(|m| {
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
    let args = members.iter().filter_map(|m| {
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

/// Implements the `core::hash::Hash` trait for the given bitfield struct.
pub fn hash(
    name: &syn::Ident,
    members: &[Member],
    cfg: Option<TokenStream>,
) -> TokenStream {
    let fields = members.iter().filter_map(|m| {
        let inner = m.inner.as_ref()?;
        if inner.from.is_empty() {
            return None;
        }

        let ident = &inner.ident;
        Some(quote!(self.#ident()))
    });

    let attr = cfg.map(|cfg| quote!(#[cfg(#cfg)]));

    quote! {
        #attr
        impl core::hash::Hash for #name {
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                #( #fields.hash(state); )*
            }
        }
    }
}

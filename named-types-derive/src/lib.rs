extern crate proc_macro;

use std::collections::HashSet;

use quote::{quote, ToTokens};
use syn::{
    parse_macro_input, parse_quote, parse_quote_spanned, punctuated::Punctuated, DeriveInput,
    GenericParam, Generics, Ident, LitStr, Path,
};

#[proc_macro_derive(Named, attributes(named))]
pub fn derive_named_trait(item: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(item as DeriveInput);

    Implementation::parse(input)
        .map(|result| result.into())
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

enum Implementation {
    Format(Ident, LitStr, Generics, Vec<GenericParamKind>),
    Passthrough(Ident, Generics, GenericParamKind),
}

impl Implementation {
    fn parse(input: DeriveInput) -> syn::parse::Result<Self> {
        let mut fmt = FormatKind::Ours(
            LitStr::new(input.ident.to_string().as_str(), input.ident.span()),
            0,
        );
        let mut ignore_all = false;
        let mut ignore = HashSet::<Ident>::with_capacity(input.generics.params.len());
        let mut passthrough: Option<Ident> = None;

        for attr in input.attrs {
            if attr.path().is_ident("named") {
                attr.parse_nested_meta(|meta| {
                    // rename struct but use our format string
                    if meta.path.is_ident("rename") {
                        fmt = FormatKind::Ours(meta.value()?.parse()?, 0);
                        Ok(())
                    // user custom format string
                    } else if meta.path.is_ident("format") {
                        fmt = FormatKind::Theirs(meta.value()?.parse()?);
                        Ok(())
                    // ignore all generics
                    } else if meta.path.is_ident("ignore_all") {
                        ignore_all = true;
                        Ok(())
                    // ignore specific generic
                    } else if meta.path.is_ident("ignore") {
                        ignore.insert(meta.value()?.parse()?);
                        Ok(())
                    // passthrough generic
                    } else if meta.path.is_ident("passthrough") {
                        passthrough = meta.value()?.parse()?;
                        Ok(())
                    } else {
                        Err(meta.error("unsupported attribute"))
                    }?;
                    if meta.input.is_empty() {
                        Ok(())
                    } else {
                        Err(syn::parse::Error::new(
                            meta.input.span(),
                            "unexpected token",
                        ))
                    }
                })?;
            }
        }

        if let Some(passthrough) = passthrough {
            let mut generics = input.generics.clone();
            let passthrough = generics
                .params
                .iter_mut()
                .find_map(|generic_param| match generic_param {
                    GenericParam::Type(type_param) => {
                        if type_param.ident == passthrough {
                            type_param.bounds.push(parse_quote!(::named_types::Named));
                            Some(GenericParamKind::Type(type_param.ident.clone()))
                        } else {
                            None
                        }
                    }
                    GenericParam::Const(const_param) => {
                        if const_param.ident == passthrough {
                            Some(GenericParamKind::Const(const_param.ident.clone()))
                        } else {
                            None
                        }
                    }
                    GenericParam::Lifetime(_) => None,
                })
                .ok_or(syn::parse::Error::new_spanned(
                    passthrough,
                    "could not find generic",
                ))?;
            return Ok(Self::Passthrough(
                input.ident.clone(),
                generics,
                passthrough,
            ));
        } else if ignore_all {
            return Ok(Self::Format(
                input.ident.clone(),
                fmt.into(),
                input.generics.clone(),
                vec![],
            ));
        }

        let mut generics = input.generics.clone();
        let mut generic_idents = Vec::with_capacity(generics.params.len());
        for mut generic in generics.params.iter_mut() {
            match &mut generic {
                GenericParam::Lifetime(_) => (),
                GenericParam::Type(generic) => {
                    if ignore.remove(&generic.ident) {
                        continue;
                    }
                    generic.bounds.push(parse_quote!(::named_types::Named));
                    generic_idents.push(GenericParamKind::Type(generic.ident.clone()));
                    fmt.add_generic();
                }
                GenericParam::Const(generic) => {
                    if ignore.remove(&generic.ident) {
                        continue;
                    }
                    generic_idents.push(GenericParamKind::Const(generic.ident.clone()));
                    fmt.add_generic();
                }
            }
        }

        let err = ignore
            .iter()
            .map(|ignore_ident| {
                syn::parse::Error::new_spanned(ignore_ident, "could not find ignored generic")
            })
            .reduce(|mut acc, err| {
                acc.extend(err);
                acc
            });

        if let Some(err) = err {
            return Err(err);
        }

        Ok(Self::Format(
            input.ident.clone(),
            fmt.into(),
            generics,
            generic_idents,
        ))
    }
}

impl Into<proc_macro2::TokenStream> for Implementation {
    fn into(self) -> proc_macro2::TokenStream {
        match self {
            Self::Format(named_type, format_string, generics, name_generics) => {
                let (impl_generics, type_generics, where_clause) = generics.split_for_impl();
                quote!(
                    #[automatically_derived]
                    impl #impl_generics ::named_types::Named for #named_type #type_generics #where_clause {
                        #[inline]
                        fn format_name(f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                            f.write_fmt(format_args!(#format_string, #(#name_generics),*))
                        }
                    }
                ).into()
            }
            Self::Passthrough(named_type, generics, passthrough) => {
                let (impl_generics, type_generics, where_clause) = generics.split_for_impl();
                match passthrough {
                    GenericParamKind::Type(passthrough) => {
                        quote!(
                            #[automatically_derived]
                            impl #impl_generics ::named_types::Named for #named_type #type_generics #where_clause {
                                const NAME: ::named_types::Name = #passthrough::NAME;

                                #[inline]
                                fn format_name(f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                                    #passthrough::format_name(f)
                                }
                            }
                        ).into()
                    },
                    GenericParamKind::Const(passthrough) => {
                        quote!(
                            #[automatically_derived]
                            impl #impl_generics ::named_types::Named for #named_type #type_generics #where_clause {
                                const NAME: ::named_types::Name = #passthrough;

                                #[inline]
                                fn format_name(f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                                    write!(f, "{}", passthrough)
                                }
                            }
                        ).into()
                    }
                }
            }
        }
    }
}

enum FormatKind {
    Ours(LitStr, usize),
    Theirs(LitStr),
}

impl FormatKind {
    fn add_generic(&mut self) {
        match self {
            Self::Ours(_, generic_count) => *generic_count += 1,
            Self::Theirs(_) => (),
        }
    }
}

impl Into<LitStr> for FormatKind {
    fn into(self) -> LitStr {
        match self {
            Self::Ours(name, mut generic_count) => {
                let span = name.span();
                let mut name = name.value();
                if generic_count != 0 {
                    name.push_str("<{}");
                    generic_count -= 1;
                    while generic_count != 0 {
                        name.push_str(", {}");
                        generic_count -= 1;
                    }
                    name.push('>');
                }
                LitStr::new(&name, span)
            }
            Self::Theirs(name) => name,
        }
    }
}

enum GenericParamKind {
    Type(Ident),
    Const(Ident),
}

impl ToTokens for GenericParamKind {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Self::Type(ident) => {
                let mut path = Punctuated::new();
                path.push(ident.clone().into());
                path.push(parse_quote_spanned!(ident.span() => NAME));
                Path {
                    leading_colon: None,
                    segments: path,
                }
                .to_tokens(tokens);
            }
            Self::Const(ident) => ident.to_tokens(tokens),
        }
    }
}

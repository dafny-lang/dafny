use std::{fmt::{Display, Formatter}, rc::Rc, ops::Deref};
pub use once_cell::unsync::Lazy;

pub struct LazyFieldWrapper<A>(pub Lazy<A, Box<dyn 'static + FnOnce() -> A>>);

impl <A: PartialEq> PartialEq for LazyFieldWrapper<A> {
    fn eq(&self, other: &Self) -> bool {
        self.0.deref() == other.0.deref()
    }
}

impl <A: Default + 'static> Default for LazyFieldWrapper<A> {
    fn default() -> Self {
        Self(Lazy::new(Box::new(A::default)))
    }
}

impl <A: DafnyPrint> DafnyPrint for LazyFieldWrapper<A> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        self.0.deref().fmt_print(f, in_seq)
    }
}

pub struct FunctionWrapper<A: ?Sized>(pub A);
impl <A> DafnyPrint for FunctionWrapper<A> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "<function>")
    }
}

impl <A: Clone> Clone for FunctionWrapper<A> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl <A> DafnyErasable for FunctionWrapper<A> {
    type Erased = FunctionWrapper<A>;

    fn erase(&self) -> &Self::Erased {
        self
    }

    fn erase_owned(self) -> Self::Erased {
        self
    }
}

impl <A> DafnyUnerasable<FunctionWrapper<A>> for FunctionWrapper<A> {
    fn unerase(v: &FunctionWrapper<A>) -> &Self {
        v
    }

    fn unerase_owned(v: FunctionWrapper<A>) -> Self {
        v
    }
}

pub struct DafnyPrintWrapper<T>(pub T);
impl <T: DafnyPrint> Display for DafnyPrintWrapper<&T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_print(f, false)
    }
}

pub trait DafnyErasable: DafnyUnerasable<Self::Erased> {
    type Erased;

    fn erase(&self) -> &Self::Erased;
    fn erase_owned(self) -> Self::Erased;
}

pub trait DafnyUnerasable<T: ?Sized> {
    fn unerase(v: &T) -> &Self;
    fn unerase_owned(v: T) -> Self;
}

impl <T> DafnyErasable for Rc<T> {
    type Erased = Rc<T>;

    #[inline]
    fn erase(&self) -> &Self::Erased {
        self
    }

    #[inline]
    fn erase_owned(self) -> Self::Erased {
        self
    }
}

impl <T> DafnyUnerasable<Rc<T>> for Rc<T> {
    #[inline]
    fn unerase(v: &Rc<T>) -> &Self {
        v
    }

    #[inline]
    fn unerase_owned(v: Rc<T>) -> Self {
        v
    }
}

impl <T> DafnyErasable for Vec<T> {
    type Erased = Vec<T>;

    #[inline]
    fn erase(&self) -> &Self::Erased {
        self
    }

    #[inline]
    fn erase_owned(self) -> Self::Erased {
        self
    }
}

impl <T> DafnyUnerasable<Vec<T>> for Vec<T> {
    #[inline]
    fn unerase(v: &Vec<T>) -> &Self {
        v
    }

    #[inline]
    fn unerase_owned(v: Vec<T>) -> Self {
        v
    }
}

impl <T> DafnyErasable for Box<T> {
    type Erased = Box<T>;

    #[inline]
    fn erase(&self) -> &Self::Erased {
        self
    }

    #[inline]
    fn erase_owned(self) -> Self::Erased {
        self
    }
}

impl <T> DafnyUnerasable<Box<T>> for Box<T> {
    #[inline]
    fn unerase(v: &Box<T>) -> &Self {
        v
    }

    #[inline]
    fn unerase_owned(v: Box<T>) -> Self {
        v
    }
}

macro_rules! impl_already_erased {
    ($name:ty) => {
        impl DafnyErasable for $name {
            type Erased = $name;

            #[inline]
            fn erase(&self) -> &Self::Erased {
                self
            }

            #[inline]
            fn erase_owned(self) -> Self::Erased {
                self
            }
        }

        impl DafnyUnerasable<$name> for $name {
            #[inline]
            fn unerase(v: &$name) -> &Self {
                v
            }
        
            #[inline]
            fn unerase_owned(v: $name) -> Self {
                v
            }
        }
    };
}

impl_already_erased! { String }
impl_already_erased! { char }
impl_already_erased! { bool }
impl_already_erased! { u8 }
impl_already_erased! { u16 }
impl_already_erased! { u32 }
impl_already_erased! { u64 }
impl_already_erased! { u128 }
impl_already_erased! { i8 }
impl_already_erased! { i16 }
impl_already_erased! { i32 }
impl_already_erased! { i64 }
impl_already_erased! { i128 }
impl_already_erased! { f32 }
impl_already_erased! { f64 }
impl_already_erased! { () }

macro_rules! impl_tuple_erased {
    ($($items:ident)*) => {
        impl <$($items,)*> DafnyErasable for ($($items,)*)
        where
            $($items: DafnyErasable,)*
        {
            type Erased = ($($items::Erased,)*);

            #[inline]
            fn erase(&self) -> &Self::Erased {
                unsafe { &*(self as *const Self as *const Self::Erased) }
            }

            #[inline]
            fn erase_owned(self) -> Self::Erased {
                unsafe { std::mem::transmute_copy(&self) }
            }
        }

        paste::item! {
            impl <$([<T $items>],)* $($items: DafnyUnerasable<[<T $items>]>,)*> DafnyUnerasable<($([<T $items>],)*)> for ($($items,)*)
            {
                #[inline]
                fn unerase(v: &($([<T $items>],)*)) -> &Self {
                    unsafe { &*(v as *const ($([<T $items>],)*) as *const Self) }
                }

                #[inline]
                fn unerase_owned(v: ($([<T $items>],)*)) -> Self {
                    unsafe { std::mem::transmute_copy(&v) }
                }
            }
        }
    };
}

macro_rules! impl_tuple_erased_loop {
    () => {};
    ($first:ident $($rest:ident)*) => {
        impl_tuple_erased_loop! { $($rest)* }
        impl_tuple_erased! { $first $($rest)* }
    };
}

// 32 elements ought to be enough for everyone
impl_tuple_erased_loop! {
    A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10
    A11 A12 A13 A14 A15 A16 A17 A18 A19 A20
    A21 A22 A23 A24 A25 A26 A27 A28 A29 A30
    A31
}

pub trait DafnyPrint {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result;

    // Vec<char> gets special treatment so we carry that information here
    #[inline]
    fn is_char() -> bool {
        false
    }
}

macro_rules! impl_print_display {
    ($name:ty) => {
        impl DafnyPrint for $name {
            fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
                self.fmt(f)
            }
        }
    };
}

impl_print_display! { String }
impl_print_display! { &str }
impl_print_display! { bool }
impl_print_display! { u8 }
impl_print_display! { u16 }
impl_print_display! { u32 }
impl_print_display! { u64 }
impl_print_display! { u128 }
impl_print_display! { i8 }
impl_print_display! { i16 }
impl_print_display! { i32 }
impl_print_display! { i64 }
impl_print_display! { i128 }

impl DafnyPrint for f32 {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{:.1}", self)
    }
}

impl DafnyPrint for f64 {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{:.1}", self)
    }
}

impl DafnyPrint for () {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "()")
    }
}

impl DafnyPrint for char {
    #[inline]
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        if in_seq {
            write!(f, "{}", self)
        } else {
            write!(f, "'{}'", self)
        }
    }

    #[inline]
    fn is_char() -> bool {
        true
    }
}

impl <T: DafnyPrint> DafnyPrint for Rc<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        self.as_ref().fmt_print(f, in_seq)
    }
}

impl <T: DafnyPrint> DafnyPrint for Vec<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        if !T::is_char() {
            write!(f, "[")?;
        }

        for (i, item) in self.iter().enumerate() {
            if !T::is_char() {
                if i > 0 {
                    write!(f, ", ")?;
                }

                item.fmt_print(f, false)?;
            } else {
                item.fmt_print(f, true)?;
            }
        }

        if !T::is_char() {
            write!(f, "]")
        } else {
            Ok(())
        }
    }
}

macro_rules! impl_tuple_print {
    ($($items:ident)*) => {
        impl <$($items,)*> DafnyPrint for ($($items,)*)
        where
            $($items: DafnyPrint,)*
        {
            #[allow(unused_assignments)]
            fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
                #[allow(non_snake_case)]
                let ($($items,)*) = self;

                write!(f, "(")?;

                let mut i = 0;
                
                $(
                    if (i > 0) {
                        write!(f, ", ")?;
                    }

                    $items.fmt_print(f, false)?;

                    i += 1;
                )*

                write!(f, ")")
            }
        }
    };
}

macro_rules! impl_tuple_print_loop {
    () => {};
    ($first:ident $($rest:ident)*) => {
        impl_tuple_print_loop! { $($rest)* }
        impl_tuple_print! { $first $($rest)* }
    };
}

// 32 elements ought to be enough for everyone
impl_tuple_print_loop! {
    A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10
    A11 A12 A13 A14 A15 A16 A17 A18 A19 A20
    A21 A22 A23 A24 A25 A26 A27 A28 A29 A30
    A31
}

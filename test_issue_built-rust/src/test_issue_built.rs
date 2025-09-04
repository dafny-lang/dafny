#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
#![cfg_attr(any(), rustfmt::skip)]

pub mod _module {
    pub use ::dafny_runtime::Set;
    pub use ::dafny_runtime::Map;
    pub use ::dafny_runtime::Sequence;
    pub use ::dafny_runtime::DafnyChar;
    pub use ::dafny_runtime::set;
    pub use ::dafny_runtime::map;
    pub use ::dafny_runtime::string_of;
    pub use ::std::rc::Rc;
    pub use ::dafny_runtime::SetBuilder;

    pub struct _default {}

    impl _default {
        /// test_issue_built.dfy(1,1)
        pub fn SomeMaps() -> Set<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>> {
            set!{map![string_of("a") => string_of("b")]}
        }
        /// test_issue_built.dfy(2,1)
        pub fn OhNo() -> Set<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>> {
            (&({
                Rc::new(move || -> Set<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>>{
            let mut _coll0: SetBuilder<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>> = SetBuilder::<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>>::new();
            for __compr_0 in (&(&({
                    Rc::new(move || -> Set<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>>{
            let mut _coll1: SetBuilder<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>> = SetBuilder::<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>>::new();
            for __compr_1 in (&_default::SomeMaps()).iter().cloned() {
                let mut m: Map<Sequence<DafnyChar>, Sequence<DafnyChar>> = __compr_1.clone();
                if _default::SomeMaps().contains(&m) {
                    _coll1.add(&m)
                }
            }
            _coll1.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                }))()).iter().cloned() {
                let mut x: Map<Sequence<DafnyChar>, Sequence<DafnyChar>> = __compr_0.clone();
                if (&({
                        Rc::new(move || -> Set<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>>{
            let mut _coll2: SetBuilder<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>> = SetBuilder::<Map<Sequence<DafnyChar>, Sequence<DafnyChar>>>::new();
            for __compr_2 in (&_default::SomeMaps()).iter().cloned() {
                let mut m: Map<Sequence<DafnyChar>, Sequence<DafnyChar>> = __compr_2.clone();
                if _default::SomeMaps().contains(&m) {
                    _coll2.add(&m)
                }
            }
            _coll2.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
                    }))().contains(&x) {
                    _coll0.add(&x)
                }
            }
            _coll0.build()
        }) as Rc<dyn ::std::ops::Fn() -> _>
            }))()
        }
    }
}
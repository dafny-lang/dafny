#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub mod _System {
  pub type nat = crate::DafnyInt;

  #[derive(PartialEq, Clone)]
  pub enum Tuple2<T0: crate::DafnyType, T1: crate::DafnyType> {
    _T2 {
      _0: T0,
      _1: T1
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType> Tuple2<T0, T1> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple2::_T2{_0, _1, } => _0,
        Tuple2::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple2::_T2{_0, _1, } => _1,
        Tuple2::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType> ::std::fmt::Debug
    for Tuple2<T0, T1> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType> crate::DafnyPrint
    for Tuple2<T0, T1> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple2::_T2{_0, _1, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple2::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType> Tuple2<T0, T1> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple2<T0, T1>) -> Tuple2<r#__T0, r#__T1>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple2<r#__T0, r#__T1>{
          match this {
            Tuple2::_T2{_0, _1, } => {
              Tuple2::_T2 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1)
              }
            },
            Tuple2::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq> Eq
    for Tuple2<T0, T1> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple2<T0, T1> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple2::_T2{_0, _1, } => {
          _0.hash(_state);
          _1.hash(_state)
        },
        Tuple2::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple2<T0, T1> {
    fn default() -> Tuple2<T0, T1> {
      Tuple2::_T2 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType> ::std::convert::AsRef<Tuple2<T0, T1>>
    for &Tuple2<T0, T1> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple0 {
    _T0 {}
  }

  impl Tuple0 {}

  impl ::std::fmt::Debug
    for Tuple0 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl crate::DafnyPrint
    for Tuple0 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple0::_T0{} => {
          write!(_formatter, "")?;
          Ok(())
        },
      }
    }
  }

  impl Eq
    for Tuple0 {}

  impl ::std::hash::Hash
    for Tuple0 {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple0::_T0{} => {
          
        },
      }
    }
  }

  impl ::std::default::Default
    for Tuple0 {
    fn default() -> Tuple0 {
      Tuple0::_T0 {}
    }
  }

  impl ::std::convert::AsRef<Tuple0>
    for &Tuple0 {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple1<T0: crate::DafnyType> {
    _T1 {
      _0: T0
    },
    _PhantomVariant(::std::marker::PhantomData<T0>)
  }

  impl<T0: crate::DafnyType> Tuple1<T0> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple1::_T1{_0, } => _0,
        Tuple1::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType> ::std::fmt::Debug
    for Tuple1<T0> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType> crate::DafnyPrint
    for Tuple1<T0> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple1::_T1{_0, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple1::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType> Tuple1<T0> {
    pub fn coerce<r#__T0: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple1<T0>) -> Tuple1<r#__T0>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple1<r#__T0>{
          match this {
            Tuple1::_T1{_0, } => {
              Tuple1::_T1 {
                _0: f_0.clone()(_0)
              }
            },
            Tuple1::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq> Eq
    for Tuple1<T0> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple1<T0> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple1::_T1{_0, } => {
          _0.hash(_state)
        },
        Tuple1::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple1<T0> {
    fn default() -> Tuple1<T0> {
      Tuple1::_T1 {
        _0: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType> ::std::convert::AsRef<Tuple1<T0>>
    for &Tuple1<T0> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple3<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType> {
    _T3 {
      _0: T0,
      _1: T1,
      _2: T2
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType> Tuple3<T0, T1, T2> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple3::_T3{_0, _1, _2, } => _0,
        Tuple3::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple3::_T3{_0, _1, _2, } => _1,
        Tuple3::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple3::_T3{_0, _1, _2, } => _2,
        Tuple3::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType> ::std::fmt::Debug
    for Tuple3<T0, T1, T2> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType> crate::DafnyPrint
    for Tuple3<T0, T1, T2> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple3::_T3{_0, _1, _2, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple3::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType> Tuple3<T0, T1, T2> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple3<T0, T1, T2>) -> Tuple3<r#__T0, r#__T1, r#__T2>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple3<r#__T0, r#__T1, r#__T2>{
          match this {
            Tuple3::_T3{_0, _1, _2, } => {
              Tuple3::_T3 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2)
              }
            },
            Tuple3::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq> Eq
    for Tuple3<T0, T1, T2> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple3<T0, T1, T2> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple3::_T3{_0, _1, _2, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state)
        },
        Tuple3::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple3<T0, T1, T2> {
    fn default() -> Tuple3<T0, T1, T2> {
      Tuple3::_T3 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType> ::std::convert::AsRef<Tuple3<T0, T1, T2>>
    for &Tuple3<T0, T1, T2> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple4<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType> {
    _T4 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType> Tuple4<T0, T1, T2, T3> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple4::_T4{_0, _1, _2, _3, } => _0,
        Tuple4::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple4::_T4{_0, _1, _2, _3, } => _1,
        Tuple4::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple4::_T4{_0, _1, _2, _3, } => _2,
        Tuple4::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple4::_T4{_0, _1, _2, _3, } => _3,
        Tuple4::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType> ::std::fmt::Debug
    for Tuple4<T0, T1, T2, T3> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType> crate::DafnyPrint
    for Tuple4<T0, T1, T2, T3> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple4::_T4{_0, _1, _2, _3, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple4::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType> Tuple4<T0, T1, T2, T3> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple4<T0, T1, T2, T3>) -> Tuple4<r#__T0, r#__T1, r#__T2, r#__T3>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple4<r#__T0, r#__T1, r#__T2, r#__T3>{
          match this {
            Tuple4::_T4{_0, _1, _2, _3, } => {
              Tuple4::_T4 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3)
              }
            },
            Tuple4::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq> Eq
    for Tuple4<T0, T1, T2, T3> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple4<T0, T1, T2, T3> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple4::_T4{_0, _1, _2, _3, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state)
        },
        Tuple4::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple4<T0, T1, T2, T3> {
    fn default() -> Tuple4<T0, T1, T2, T3> {
      Tuple4::_T4 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType> ::std::convert::AsRef<Tuple4<T0, T1, T2, T3>>
    for &Tuple4<T0, T1, T2, T3> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple5<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType> {
    _T5 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType> Tuple5<T0, T1, T2, T3, T4> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple5::_T5{_0, _1, _2, _3, _4, } => _0,
        Tuple5::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple5::_T5{_0, _1, _2, _3, _4, } => _1,
        Tuple5::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple5::_T5{_0, _1, _2, _3, _4, } => _2,
        Tuple5::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple5::_T5{_0, _1, _2, _3, _4, } => _3,
        Tuple5::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple5::_T5{_0, _1, _2, _3, _4, } => _4,
        Tuple5::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType> ::std::fmt::Debug
    for Tuple5<T0, T1, T2, T3, T4> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType> crate::DafnyPrint
    for Tuple5<T0, T1, T2, T3, T4> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple5::_T5{_0, _1, _2, _3, _4, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple5::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType> Tuple5<T0, T1, T2, T3, T4> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple5<T0, T1, T2, T3, T4>) -> Tuple5<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple5<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4>{
          match this {
            Tuple5::_T5{_0, _1, _2, _3, _4, } => {
              Tuple5::_T5 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4)
              }
            },
            Tuple5::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq> Eq
    for Tuple5<T0, T1, T2, T3, T4> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple5<T0, T1, T2, T3, T4> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple5::_T5{_0, _1, _2, _3, _4, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state)
        },
        Tuple5::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple5<T0, T1, T2, T3, T4> {
    fn default() -> Tuple5<T0, T1, T2, T3, T4> {
      Tuple5::_T5 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType> ::std::convert::AsRef<Tuple5<T0, T1, T2, T3, T4>>
    for &Tuple5<T0, T1, T2, T3, T4> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple6<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType> {
    _T6 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType> Tuple6<T0, T1, T2, T3, T4, T5> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _0,
        Tuple6::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _1,
        Tuple6::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _2,
        Tuple6::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _3,
        Tuple6::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _4,
        Tuple6::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => _5,
        Tuple6::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType> ::std::fmt::Debug
    for Tuple6<T0, T1, T2, T3, T4, T5> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType> crate::DafnyPrint
    for Tuple6<T0, T1, T2, T3, T4, T5> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple6::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType> Tuple6<T0, T1, T2, T3, T4, T5> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple6<T0, T1, T2, T3, T4, T5>) -> Tuple6<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple6<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5>{
          match this {
            Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => {
              Tuple6::_T6 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5)
              }
            },
            Tuple6::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq> Eq
    for Tuple6<T0, T1, T2, T3, T4, T5> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple6<T0, T1, T2, T3, T4, T5> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple6::_T6{_0, _1, _2, _3, _4, _5, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state)
        },
        Tuple6::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple6<T0, T1, T2, T3, T4, T5> {
    fn default() -> Tuple6<T0, T1, T2, T3, T4, T5> {
      Tuple6::_T6 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType> ::std::convert::AsRef<Tuple6<T0, T1, T2, T3, T4, T5>>
    for &Tuple6<T0, T1, T2, T3, T4, T5> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple7<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType> {
    _T7 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType> Tuple7<T0, T1, T2, T3, T4, T5, T6> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _0,
        Tuple7::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _1,
        Tuple7::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _2,
        Tuple7::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _3,
        Tuple7::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _4,
        Tuple7::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _5,
        Tuple7::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => _6,
        Tuple7::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType> ::std::fmt::Debug
    for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType> crate::DafnyPrint
    for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple7::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType> Tuple7<T0, T1, T2, T3, T4, T5, T6> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple7<T0, T1, T2, T3, T4, T5, T6>) -> Tuple7<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple7<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6>{
          match this {
            Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => {
              Tuple7::_T7 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6)
              }
            },
            Tuple7::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq> Eq
    for Tuple7<T0, T1, T2, T3, T4, T5, T6> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple7::_T7{_0, _1, _2, _3, _4, _5, _6, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state)
        },
        Tuple7::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple7<T0, T1, T2, T3, T4, T5, T6> {
    fn default() -> Tuple7<T0, T1, T2, T3, T4, T5, T6> {
      Tuple7::_T7 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType> ::std::convert::AsRef<Tuple7<T0, T1, T2, T3, T4, T5, T6>>
    for &Tuple7<T0, T1, T2, T3, T4, T5, T6> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple8<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType> {
    _T8 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType> Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _0,
        Tuple8::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _1,
        Tuple8::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _2,
        Tuple8::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _3,
        Tuple8::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _4,
        Tuple8::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _5,
        Tuple8::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _6,
        Tuple8::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => _7,
        Tuple8::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType> ::std::fmt::Debug
    for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType> crate::DafnyPrint
    for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple8::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType> Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>) -> Tuple8<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple8<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7>{
          match this {
            Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => {
              Tuple8::_T8 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7)
              }
            },
            Tuple8::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq> Eq
    for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple8::_T8{_0, _1, _2, _3, _4, _5, _6, _7, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state)
        },
        Tuple8::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    fn default() -> Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
      Tuple8::_T8 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType> ::std::convert::AsRef<Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>>
    for &Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple9<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType> {
    _T9 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType> Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _0,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _1,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _2,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _3,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _4,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _5,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _6,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _7,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => _8,
        Tuple9::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType> ::std::fmt::Debug
    for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType> crate::DafnyPrint
    for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple9::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType> Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>) -> Tuple9<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple9<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8>{
          match this {
            Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => {
              Tuple9::_T9 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8)
              }
            },
            Tuple9::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq> Eq
    for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple9::_T9{_0, _1, _2, _3, _4, _5, _6, _7, _8, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state)
        },
        Tuple9::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    fn default() -> Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
      Tuple9::_T9 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType> ::std::convert::AsRef<Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>
    for &Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple10<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType> {
    _T10 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType> Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _0,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _1,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _2,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _3,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _4,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _5,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _6,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _7,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _8,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => _9,
        Tuple10::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType> ::std::fmt::Debug
    for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType> crate::DafnyPrint
    for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple10::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType> Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>) -> Tuple10<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple10<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9>{
          match this {
            Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => {
              Tuple10::_T10 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9)
              }
            },
            Tuple10::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq> Eq
    for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple10::_T10{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state)
        },
        Tuple10::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    fn default() -> Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
      Tuple10::_T10 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType> ::std::convert::AsRef<Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>
    for &Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple11<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType> {
    _T11 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType> Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _0,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _1,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _2,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _3,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _4,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _5,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _6,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _7,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _8,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _9,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => _10,
        Tuple11::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType> ::std::fmt::Debug
    for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType> crate::DafnyPrint
    for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple11::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType> Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>) -> Tuple11<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple11<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10>{
          match this {
            Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => {
              Tuple11::_T11 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10)
              }
            },
            Tuple11::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq> Eq
    for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple11::_T11{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state)
        },
        Tuple11::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    fn default() -> Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
      Tuple11::_T11 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType> ::std::convert::AsRef<Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>
    for &Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple12<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType> {
    _T12 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType> Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _0,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _1,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _2,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _3,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _4,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _5,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _6,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _7,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _8,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _9,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _10,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => _11,
        Tuple12::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType> ::std::fmt::Debug
    for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType> crate::DafnyPrint
    for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple12::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType> Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>) -> Tuple12<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple12<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11>{
          match this {
            Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => {
              Tuple12::_T12 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11)
              }
            },
            Tuple12::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq> Eq
    for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple12::_T12{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state)
        },
        Tuple12::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    fn default() -> Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
      Tuple12::_T12 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType> ::std::convert::AsRef<Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>
    for &Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple13<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType> {
    _T13 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11,
      _12: T12
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>,
      ::std::marker::PhantomData<T12>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType> Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _0,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _1,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _2,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _3,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _4,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _5,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _6,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _7,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _8,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _9,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _10,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _11,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _12(&self) -> &T12 {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => _12,
        Tuple13::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType> ::std::fmt::Debug
    for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType> crate::DafnyPrint
    for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_12, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple13::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType> Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType, r#__T12: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>, f_12: ::std::rc::Rc<impl ::std::ops::Fn(T12) -> r#__T12 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>) -> Tuple13<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple13<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12>{
          match this {
            Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => {
              Tuple13::_T13 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11),
                _12: f_12.clone()(_12)
              }
            },
            Tuple13::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq, T12: crate::DafnyType + Eq> Eq
    for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash, T12: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple13::_T13{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state);
          _12.hash(_state)
        },
        Tuple13::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default, T12: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    fn default() -> Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
      Tuple13::_T13 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default(),
        _12: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType> ::std::convert::AsRef<Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>
    for &Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple14<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType> {
    _T14 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11,
      _12: T12,
      _13: T13
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>,
      ::std::marker::PhantomData<T12>,
      ::std::marker::PhantomData<T13>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType> Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _0,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _1,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _2,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _3,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _4,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _5,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _6,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _7,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _8,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _9,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _10,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _11,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _12(&self) -> &T12 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _12,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _13(&self) -> &T13 {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => _13,
        Tuple14::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType> ::std::fmt::Debug
    for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType> crate::DafnyPrint
    for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_12, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_13, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple14::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType> Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType, r#__T12: crate::DafnyType, r#__T13: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>, f_12: ::std::rc::Rc<impl ::std::ops::Fn(T12) -> r#__T12 + 'static>, f_13: ::std::rc::Rc<impl ::std::ops::Fn(T13) -> r#__T13 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>) -> Tuple14<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple14<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13>{
          match this {
            Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => {
              Tuple14::_T14 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11),
                _12: f_12.clone()(_12),
                _13: f_13.clone()(_13)
              }
            },
            Tuple14::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq, T12: crate::DafnyType + Eq, T13: crate::DafnyType + Eq> Eq
    for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash, T12: crate::DafnyType + ::std::hash::Hash, T13: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple14::_T14{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state);
          _12.hash(_state);
          _13.hash(_state)
        },
        Tuple14::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default, T12: crate::DafnyType + ::std::default::Default, T13: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    fn default() -> Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
      Tuple14::_T14 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default(),
        _12: ::std::default::Default::default(),
        _13: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType> ::std::convert::AsRef<Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>
    for &Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple15<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType> {
    _T15 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11,
      _12: T12,
      _13: T13,
      _14: T14
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>,
      ::std::marker::PhantomData<T12>,
      ::std::marker::PhantomData<T13>,
      ::std::marker::PhantomData<T14>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType> Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _0,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _1,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _2,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _3,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _4,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _5,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _6,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _7,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _8,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _9,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _10,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _11,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _12(&self) -> &T12 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _12,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _13(&self) -> &T13 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _13,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _14(&self) -> &T14 {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => _14,
        Tuple15::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType> ::std::fmt::Debug
    for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType> crate::DafnyPrint
    for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_12, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_13, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_14, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple15::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType> Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType, r#__T12: crate::DafnyType, r#__T13: crate::DafnyType, r#__T14: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>, f_12: ::std::rc::Rc<impl ::std::ops::Fn(T12) -> r#__T12 + 'static>, f_13: ::std::rc::Rc<impl ::std::ops::Fn(T13) -> r#__T13 + 'static>, f_14: ::std::rc::Rc<impl ::std::ops::Fn(T14) -> r#__T14 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>) -> Tuple15<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple15<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14>{
          match this {
            Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => {
              Tuple15::_T15 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11),
                _12: f_12.clone()(_12),
                _13: f_13.clone()(_13),
                _14: f_14.clone()(_14)
              }
            },
            Tuple15::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq, T12: crate::DafnyType + Eq, T13: crate::DafnyType + Eq, T14: crate::DafnyType + Eq> Eq
    for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash, T12: crate::DafnyType + ::std::hash::Hash, T13: crate::DafnyType + ::std::hash::Hash, T14: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple15::_T15{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state);
          _12.hash(_state);
          _13.hash(_state);
          _14.hash(_state)
        },
        Tuple15::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default, T12: crate::DafnyType + ::std::default::Default, T13: crate::DafnyType + ::std::default::Default, T14: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    fn default() -> Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
      Tuple15::_T15 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default(),
        _12: ::std::default::Default::default(),
        _13: ::std::default::Default::default(),
        _14: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType> ::std::convert::AsRef<Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>
    for &Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple16<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType> {
    _T16 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11,
      _12: T12,
      _13: T13,
      _14: T14,
      _15: T15
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>,
      ::std::marker::PhantomData<T12>,
      ::std::marker::PhantomData<T13>,
      ::std::marker::PhantomData<T14>,
      ::std::marker::PhantomData<T15>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType> Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _0,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _1,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _2,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _3,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _4,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _5,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _6,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _7,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _8,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _9,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _10,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _11,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _12(&self) -> &T12 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _12,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _13(&self) -> &T13 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _13,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _14(&self) -> &T14 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _14,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _15(&self) -> &T15 {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => _15,
        Tuple16::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType> ::std::fmt::Debug
    for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType> crate::DafnyPrint
    for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_12, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_13, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_14, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_15, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple16::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType> Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType, r#__T12: crate::DafnyType, r#__T13: crate::DafnyType, r#__T14: crate::DafnyType, r#__T15: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>, f_12: ::std::rc::Rc<impl ::std::ops::Fn(T12) -> r#__T12 + 'static>, f_13: ::std::rc::Rc<impl ::std::ops::Fn(T13) -> r#__T13 + 'static>, f_14: ::std::rc::Rc<impl ::std::ops::Fn(T14) -> r#__T14 + 'static>, f_15: ::std::rc::Rc<impl ::std::ops::Fn(T15) -> r#__T15 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>) -> Tuple16<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple16<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15>{
          match this {
            Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => {
              Tuple16::_T16 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11),
                _12: f_12.clone()(_12),
                _13: f_13.clone()(_13),
                _14: f_14.clone()(_14),
                _15: f_15.clone()(_15)
              }
            },
            Tuple16::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq, T12: crate::DafnyType + Eq, T13: crate::DafnyType + Eq, T14: crate::DafnyType + Eq, T15: crate::DafnyType + Eq> Eq
    for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash, T12: crate::DafnyType + ::std::hash::Hash, T13: crate::DafnyType + ::std::hash::Hash, T14: crate::DafnyType + ::std::hash::Hash, T15: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple16::_T16{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state);
          _12.hash(_state);
          _13.hash(_state);
          _14.hash(_state);
          _15.hash(_state)
        },
        Tuple16::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default, T12: crate::DafnyType + ::std::default::Default, T13: crate::DafnyType + ::std::default::Default, T14: crate::DafnyType + ::std::default::Default, T15: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    fn default() -> Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
      Tuple16::_T16 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default(),
        _12: ::std::default::Default::default(),
        _13: ::std::default::Default::default(),
        _14: ::std::default::Default::default(),
        _15: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType> ::std::convert::AsRef<Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>
    for &Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple17<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType> {
    _T17 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11,
      _12: T12,
      _13: T13,
      _14: T14,
      _15: T15,
      _16: T16
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>,
      ::std::marker::PhantomData<T12>,
      ::std::marker::PhantomData<T13>,
      ::std::marker::PhantomData<T14>,
      ::std::marker::PhantomData<T15>,
      ::std::marker::PhantomData<T16>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType> Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _0,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _1,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _2,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _3,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _4,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _5,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _6,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _7,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _8,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _9,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _10,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _11,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _12(&self) -> &T12 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _12,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _13(&self) -> &T13 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _13,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _14(&self) -> &T14 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _14,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _15(&self) -> &T15 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _15,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _16(&self) -> &T16 {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => _16,
        Tuple17::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType> ::std::fmt::Debug
    for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType> crate::DafnyPrint
    for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_12, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_13, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_14, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_15, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_16, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple17::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType> Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType, r#__T12: crate::DafnyType, r#__T13: crate::DafnyType, r#__T14: crate::DafnyType, r#__T15: crate::DafnyType, r#__T16: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>, f_12: ::std::rc::Rc<impl ::std::ops::Fn(T12) -> r#__T12 + 'static>, f_13: ::std::rc::Rc<impl ::std::ops::Fn(T13) -> r#__T13 + 'static>, f_14: ::std::rc::Rc<impl ::std::ops::Fn(T14) -> r#__T14 + 'static>, f_15: ::std::rc::Rc<impl ::std::ops::Fn(T15) -> r#__T15 + 'static>, f_16: ::std::rc::Rc<impl ::std::ops::Fn(T16) -> r#__T16 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>) -> Tuple17<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15, r#__T16>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple17<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15, r#__T16>{
          match this {
            Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => {
              Tuple17::_T17 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11),
                _12: f_12.clone()(_12),
                _13: f_13.clone()(_13),
                _14: f_14.clone()(_14),
                _15: f_15.clone()(_15),
                _16: f_16.clone()(_16)
              }
            },
            Tuple17::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq, T12: crate::DafnyType + Eq, T13: crate::DafnyType + Eq, T14: crate::DafnyType + Eq, T15: crate::DafnyType + Eq, T16: crate::DafnyType + Eq> Eq
    for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash, T12: crate::DafnyType + ::std::hash::Hash, T13: crate::DafnyType + ::std::hash::Hash, T14: crate::DafnyType + ::std::hash::Hash, T15: crate::DafnyType + ::std::hash::Hash, T16: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple17::_T17{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state);
          _12.hash(_state);
          _13.hash(_state);
          _14.hash(_state);
          _15.hash(_state);
          _16.hash(_state)
        },
        Tuple17::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default, T12: crate::DafnyType + ::std::default::Default, T13: crate::DafnyType + ::std::default::Default, T14: crate::DafnyType + ::std::default::Default, T15: crate::DafnyType + ::std::default::Default, T16: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    fn default() -> Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
      Tuple17::_T17 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default(),
        _12: ::std::default::Default::default(),
        _13: ::std::default::Default::default(),
        _14: ::std::default::Default::default(),
        _15: ::std::default::Default::default(),
        _16: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType> ::std::convert::AsRef<Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>
    for &Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple18<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType> {
    _T18 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11,
      _12: T12,
      _13: T13,
      _14: T14,
      _15: T15,
      _16: T16,
      _17: T17
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>,
      ::std::marker::PhantomData<T12>,
      ::std::marker::PhantomData<T13>,
      ::std::marker::PhantomData<T14>,
      ::std::marker::PhantomData<T15>,
      ::std::marker::PhantomData<T16>,
      ::std::marker::PhantomData<T17>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType> Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _0,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _1,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _2,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _3,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _4,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _5,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _6,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _7,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _8,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _9,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _10,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _11,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _12(&self) -> &T12 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _12,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _13(&self) -> &T13 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _13,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _14(&self) -> &T14 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _14,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _15(&self) -> &T15 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _15,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _16(&self) -> &T16 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _16,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _17(&self) -> &T17 {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => _17,
        Tuple18::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType> ::std::fmt::Debug
    for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType> crate::DafnyPrint
    for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_12, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_13, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_14, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_15, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_16, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_17, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple18::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType> Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType, r#__T12: crate::DafnyType, r#__T13: crate::DafnyType, r#__T14: crate::DafnyType, r#__T15: crate::DafnyType, r#__T16: crate::DafnyType, r#__T17: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>, f_12: ::std::rc::Rc<impl ::std::ops::Fn(T12) -> r#__T12 + 'static>, f_13: ::std::rc::Rc<impl ::std::ops::Fn(T13) -> r#__T13 + 'static>, f_14: ::std::rc::Rc<impl ::std::ops::Fn(T14) -> r#__T14 + 'static>, f_15: ::std::rc::Rc<impl ::std::ops::Fn(T15) -> r#__T15 + 'static>, f_16: ::std::rc::Rc<impl ::std::ops::Fn(T16) -> r#__T16 + 'static>, f_17: ::std::rc::Rc<impl ::std::ops::Fn(T17) -> r#__T17 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>) -> Tuple18<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15, r#__T16, r#__T17>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple18<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15, r#__T16, r#__T17>{
          match this {
            Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => {
              Tuple18::_T18 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11),
                _12: f_12.clone()(_12),
                _13: f_13.clone()(_13),
                _14: f_14.clone()(_14),
                _15: f_15.clone()(_15),
                _16: f_16.clone()(_16),
                _17: f_17.clone()(_17)
              }
            },
            Tuple18::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq, T12: crate::DafnyType + Eq, T13: crate::DafnyType + Eq, T14: crate::DafnyType + Eq, T15: crate::DafnyType + Eq, T16: crate::DafnyType + Eq, T17: crate::DafnyType + Eq> Eq
    for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash, T12: crate::DafnyType + ::std::hash::Hash, T13: crate::DafnyType + ::std::hash::Hash, T14: crate::DafnyType + ::std::hash::Hash, T15: crate::DafnyType + ::std::hash::Hash, T16: crate::DafnyType + ::std::hash::Hash, T17: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple18::_T18{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state);
          _12.hash(_state);
          _13.hash(_state);
          _14.hash(_state);
          _15.hash(_state);
          _16.hash(_state);
          _17.hash(_state)
        },
        Tuple18::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default, T12: crate::DafnyType + ::std::default::Default, T13: crate::DafnyType + ::std::default::Default, T14: crate::DafnyType + ::std::default::Default, T15: crate::DafnyType + ::std::default::Default, T16: crate::DafnyType + ::std::default::Default, T17: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    fn default() -> Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
      Tuple18::_T18 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default(),
        _12: ::std::default::Default::default(),
        _13: ::std::default::Default::default(),
        _14: ::std::default::Default::default(),
        _15: ::std::default::Default::default(),
        _16: ::std::default::Default::default(),
        _17: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType> ::std::convert::AsRef<Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>
    for &Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple19<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType> {
    _T19 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11,
      _12: T12,
      _13: T13,
      _14: T14,
      _15: T15,
      _16: T16,
      _17: T17,
      _18: T18
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>,
      ::std::marker::PhantomData<T12>,
      ::std::marker::PhantomData<T13>,
      ::std::marker::PhantomData<T14>,
      ::std::marker::PhantomData<T15>,
      ::std::marker::PhantomData<T16>,
      ::std::marker::PhantomData<T17>,
      ::std::marker::PhantomData<T18>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType> Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _0,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _1,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _2,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _3,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _4,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _5,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _6,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _7,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _8,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _9,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _10,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _11,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _12(&self) -> &T12 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _12,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _13(&self) -> &T13 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _13,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _14(&self) -> &T14 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _14,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _15(&self) -> &T15 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _15,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _16(&self) -> &T16 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _16,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _17(&self) -> &T17 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _17,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _18(&self) -> &T18 {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => _18,
        Tuple19::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType> ::std::fmt::Debug
    for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType> crate::DafnyPrint
    for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_12, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_13, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_14, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_15, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_16, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_17, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_18, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple19::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType> Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType, r#__T12: crate::DafnyType, r#__T13: crate::DafnyType, r#__T14: crate::DafnyType, r#__T15: crate::DafnyType, r#__T16: crate::DafnyType, r#__T17: crate::DafnyType, r#__T18: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>, f_12: ::std::rc::Rc<impl ::std::ops::Fn(T12) -> r#__T12 + 'static>, f_13: ::std::rc::Rc<impl ::std::ops::Fn(T13) -> r#__T13 + 'static>, f_14: ::std::rc::Rc<impl ::std::ops::Fn(T14) -> r#__T14 + 'static>, f_15: ::std::rc::Rc<impl ::std::ops::Fn(T15) -> r#__T15 + 'static>, f_16: ::std::rc::Rc<impl ::std::ops::Fn(T16) -> r#__T16 + 'static>, f_17: ::std::rc::Rc<impl ::std::ops::Fn(T17) -> r#__T17 + 'static>, f_18: ::std::rc::Rc<impl ::std::ops::Fn(T18) -> r#__T18 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>) -> Tuple19<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15, r#__T16, r#__T17, r#__T18>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple19<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15, r#__T16, r#__T17, r#__T18>{
          match this {
            Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => {
              Tuple19::_T19 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11),
                _12: f_12.clone()(_12),
                _13: f_13.clone()(_13),
                _14: f_14.clone()(_14),
                _15: f_15.clone()(_15),
                _16: f_16.clone()(_16),
                _17: f_17.clone()(_17),
                _18: f_18.clone()(_18)
              }
            },
            Tuple19::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq, T12: crate::DafnyType + Eq, T13: crate::DafnyType + Eq, T14: crate::DafnyType + Eq, T15: crate::DafnyType + Eq, T16: crate::DafnyType + Eq, T17: crate::DafnyType + Eq, T18: crate::DafnyType + Eq> Eq
    for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash, T12: crate::DafnyType + ::std::hash::Hash, T13: crate::DafnyType + ::std::hash::Hash, T14: crate::DafnyType + ::std::hash::Hash, T15: crate::DafnyType + ::std::hash::Hash, T16: crate::DafnyType + ::std::hash::Hash, T17: crate::DafnyType + ::std::hash::Hash, T18: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple19::_T19{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state);
          _12.hash(_state);
          _13.hash(_state);
          _14.hash(_state);
          _15.hash(_state);
          _16.hash(_state);
          _17.hash(_state);
          _18.hash(_state)
        },
        Tuple19::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default, T12: crate::DafnyType + ::std::default::Default, T13: crate::DafnyType + ::std::default::Default, T14: crate::DafnyType + ::std::default::Default, T15: crate::DafnyType + ::std::default::Default, T16: crate::DafnyType + ::std::default::Default, T17: crate::DafnyType + ::std::default::Default, T18: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    fn default() -> Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
      Tuple19::_T19 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default(),
        _12: ::std::default::Default::default(),
        _13: ::std::default::Default::default(),
        _14: ::std::default::Default::default(),
        _15: ::std::default::Default::default(),
        _16: ::std::default::Default::default(),
        _17: ::std::default::Default::default(),
        _18: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType> ::std::convert::AsRef<Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>
    for &Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    fn as_ref(&self) -> Self {
      self
    }
  }

  #[derive(PartialEq, Clone)]
  pub enum Tuple20<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType, T19: crate::DafnyType> {
    _T20 {
      _0: T0,
      _1: T1,
      _2: T2,
      _3: T3,
      _4: T4,
      _5: T5,
      _6: T6,
      _7: T7,
      _8: T8,
      _9: T9,
      _10: T10,
      _11: T11,
      _12: T12,
      _13: T13,
      _14: T14,
      _15: T15,
      _16: T16,
      _17: T17,
      _18: T18,
      _19: T19
    },
    _PhantomVariant(::std::marker::PhantomData<T0>,
      ::std::marker::PhantomData<T1>,
      ::std::marker::PhantomData<T2>,
      ::std::marker::PhantomData<T3>,
      ::std::marker::PhantomData<T4>,
      ::std::marker::PhantomData<T5>,
      ::std::marker::PhantomData<T6>,
      ::std::marker::PhantomData<T7>,
      ::std::marker::PhantomData<T8>,
      ::std::marker::PhantomData<T9>,
      ::std::marker::PhantomData<T10>,
      ::std::marker::PhantomData<T11>,
      ::std::marker::PhantomData<T12>,
      ::std::marker::PhantomData<T13>,
      ::std::marker::PhantomData<T14>,
      ::std::marker::PhantomData<T15>,
      ::std::marker::PhantomData<T16>,
      ::std::marker::PhantomData<T17>,
      ::std::marker::PhantomData<T18>,
      ::std::marker::PhantomData<T19>)
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType, T19: crate::DafnyType> Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _0,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _1,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _2(&self) -> &T2 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _2,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _3(&self) -> &T3 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _3,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _4(&self) -> &T4 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _4,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _5(&self) -> &T5 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _5,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _6(&self) -> &T6 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _6,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _7(&self) -> &T7 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _7,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _8(&self) -> &T8 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _8,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _9(&self) -> &T9 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _9,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _10(&self) -> &T10 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _10,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _11(&self) -> &T11 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _11,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _12(&self) -> &T12 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _12,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _13(&self) -> &T13 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _13,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _14(&self) -> &T14 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _14,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _15(&self) -> &T15 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _15,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _16(&self) -> &T16 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _16,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _17(&self) -> &T17 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _17,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _18(&self) -> &T18 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _18,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
    pub fn _19(&self) -> &T19 {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => _19,
        Tuple20::_PhantomVariant(..) => panic!(),
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType, T19: crate::DafnyType> ::std::fmt::Debug
    for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
      crate::DafnyPrint::fmt_print(self, f, true)
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType, T19: crate::DafnyType> crate::DafnyPrint
    for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => {
          write!(_formatter, "(")?;
          crate::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_2, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_3, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_4, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_5, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_6, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_7, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_8, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_9, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_10, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_11, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_12, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_13, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_14, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_15, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_16, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_17, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_18, _formatter, false)?;
          write!(_formatter, ", ")?;
          crate::DafnyPrint::fmt_print(_19, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple20::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType, T19: crate::DafnyType> Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    pub fn coerce<r#__T0: crate::DafnyType, r#__T1: crate::DafnyType, r#__T2: crate::DafnyType, r#__T3: crate::DafnyType, r#__T4: crate::DafnyType, r#__T5: crate::DafnyType, r#__T6: crate::DafnyType, r#__T7: crate::DafnyType, r#__T8: crate::DafnyType, r#__T9: crate::DafnyType, r#__T10: crate::DafnyType, r#__T11: crate::DafnyType, r#__T12: crate::DafnyType, r#__T13: crate::DafnyType, r#__T14: crate::DafnyType, r#__T15: crate::DafnyType, r#__T16: crate::DafnyType, r#__T17: crate::DafnyType, r#__T18: crate::DafnyType, r#__T19: crate::DafnyType>(f_0: ::std::rc::Rc<impl ::std::ops::Fn(T0) -> r#__T0 + 'static>, f_1: ::std::rc::Rc<impl ::std::ops::Fn(T1) -> r#__T1 + 'static>, f_2: ::std::rc::Rc<impl ::std::ops::Fn(T2) -> r#__T2 + 'static>, f_3: ::std::rc::Rc<impl ::std::ops::Fn(T3) -> r#__T3 + 'static>, f_4: ::std::rc::Rc<impl ::std::ops::Fn(T4) -> r#__T4 + 'static>, f_5: ::std::rc::Rc<impl ::std::ops::Fn(T5) -> r#__T5 + 'static>, f_6: ::std::rc::Rc<impl ::std::ops::Fn(T6) -> r#__T6 + 'static>, f_7: ::std::rc::Rc<impl ::std::ops::Fn(T7) -> r#__T7 + 'static>, f_8: ::std::rc::Rc<impl ::std::ops::Fn(T8) -> r#__T8 + 'static>, f_9: ::std::rc::Rc<impl ::std::ops::Fn(T9) -> r#__T9 + 'static>, f_10: ::std::rc::Rc<impl ::std::ops::Fn(T10) -> r#__T10 + 'static>, f_11: ::std::rc::Rc<impl ::std::ops::Fn(T11) -> r#__T11 + 'static>, f_12: ::std::rc::Rc<impl ::std::ops::Fn(T12) -> r#__T12 + 'static>, f_13: ::std::rc::Rc<impl ::std::ops::Fn(T13) -> r#__T13 + 'static>, f_14: ::std::rc::Rc<impl ::std::ops::Fn(T14) -> r#__T14 + 'static>, f_15: ::std::rc::Rc<impl ::std::ops::Fn(T15) -> r#__T15 + 'static>, f_16: ::std::rc::Rc<impl ::std::ops::Fn(T16) -> r#__T16 + 'static>, f_17: ::std::rc::Rc<impl ::std::ops::Fn(T17) -> r#__T17 + 'static>, f_18: ::std::rc::Rc<impl ::std::ops::Fn(T18) -> r#__T18 + 'static>, f_19: ::std::rc::Rc<impl ::std::ops::Fn(T19) -> r#__T19 + 'static>) -> ::std::rc::Rc<impl ::std::ops::Fn(Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>) -> Tuple20<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15, r#__T16, r#__T17, r#__T18, r#__T19>> {
      ::std::rc::Rc::new(move |this: Self| -> Tuple20<r#__T0, r#__T1, r#__T2, r#__T3, r#__T4, r#__T5, r#__T6, r#__T7, r#__T8, r#__T9, r#__T10, r#__T11, r#__T12, r#__T13, r#__T14, r#__T15, r#__T16, r#__T17, r#__T18, r#__T19>{
          match this {
            Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => {
              Tuple20::_T20 {
                _0: f_0.clone()(_0),
                _1: f_1.clone()(_1),
                _2: f_2.clone()(_2),
                _3: f_3.clone()(_3),
                _4: f_4.clone()(_4),
                _5: f_5.clone()(_5),
                _6: f_6.clone()(_6),
                _7: f_7.clone()(_7),
                _8: f_8.clone()(_8),
                _9: f_9.clone()(_9),
                _10: f_10.clone()(_10),
                _11: f_11.clone()(_11),
                _12: f_12.clone()(_12),
                _13: f_13.clone()(_13),
                _14: f_14.clone()(_14),
                _15: f_15.clone()(_15),
                _16: f_16.clone()(_16),
                _17: f_17.clone()(_17),
                _18: f_18.clone()(_18),
                _19: f_19.clone()(_19)
              }
            },
            Tuple20::_PhantomVariant(..) => {panic!()},
          }
        })
    }
  }

  impl<T0: crate::DafnyType + Eq, T1: crate::DafnyType + Eq, T2: crate::DafnyType + Eq, T3: crate::DafnyType + Eq, T4: crate::DafnyType + Eq, T5: crate::DafnyType + Eq, T6: crate::DafnyType + Eq, T7: crate::DafnyType + Eq, T8: crate::DafnyType + Eq, T9: crate::DafnyType + Eq, T10: crate::DafnyType + Eq, T11: crate::DafnyType + Eq, T12: crate::DafnyType + Eq, T13: crate::DafnyType + Eq, T14: crate::DafnyType + Eq, T15: crate::DafnyType + Eq, T16: crate::DafnyType + Eq, T17: crate::DafnyType + Eq, T18: crate::DafnyType + Eq, T19: crate::DafnyType + Eq> Eq
    for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {}

  impl<T0: crate::DafnyType + ::std::hash::Hash, T1: crate::DafnyType + ::std::hash::Hash, T2: crate::DafnyType + ::std::hash::Hash, T3: crate::DafnyType + ::std::hash::Hash, T4: crate::DafnyType + ::std::hash::Hash, T5: crate::DafnyType + ::std::hash::Hash, T6: crate::DafnyType + ::std::hash::Hash, T7: crate::DafnyType + ::std::hash::Hash, T8: crate::DafnyType + ::std::hash::Hash, T9: crate::DafnyType + ::std::hash::Hash, T10: crate::DafnyType + ::std::hash::Hash, T11: crate::DafnyType + ::std::hash::Hash, T12: crate::DafnyType + ::std::hash::Hash, T13: crate::DafnyType + ::std::hash::Hash, T14: crate::DafnyType + ::std::hash::Hash, T15: crate::DafnyType + ::std::hash::Hash, T16: crate::DafnyType + ::std::hash::Hash, T17: crate::DafnyType + ::std::hash::Hash, T18: crate::DafnyType + ::std::hash::Hash, T19: crate::DafnyType + ::std::hash::Hash> ::std::hash::Hash
    for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
      match self {
        Tuple20::_T20{_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19, } => {
          _0.hash(_state);
          _1.hash(_state);
          _2.hash(_state);
          _3.hash(_state);
          _4.hash(_state);
          _5.hash(_state);
          _6.hash(_state);
          _7.hash(_state);
          _8.hash(_state);
          _9.hash(_state);
          _10.hash(_state);
          _11.hash(_state);
          _12.hash(_state);
          _13.hash(_state);
          _14.hash(_state);
          _15.hash(_state);
          _16.hash(_state);
          _17.hash(_state);
          _18.hash(_state);
          _19.hash(_state)
        },
        Tuple20::_PhantomVariant(..) => {panic!()},
      }
    }
  }

  impl<T0: crate::DafnyType + ::std::default::Default, T1: crate::DafnyType + ::std::default::Default, T2: crate::DafnyType + ::std::default::Default, T3: crate::DafnyType + ::std::default::Default, T4: crate::DafnyType + ::std::default::Default, T5: crate::DafnyType + ::std::default::Default, T6: crate::DafnyType + ::std::default::Default, T7: crate::DafnyType + ::std::default::Default, T8: crate::DafnyType + ::std::default::Default, T9: crate::DafnyType + ::std::default::Default, T10: crate::DafnyType + ::std::default::Default, T11: crate::DafnyType + ::std::default::Default, T12: crate::DafnyType + ::std::default::Default, T13: crate::DafnyType + ::std::default::Default, T14: crate::DafnyType + ::std::default::Default, T15: crate::DafnyType + ::std::default::Default, T16: crate::DafnyType + ::std::default::Default, T17: crate::DafnyType + ::std::default::Default, T18: crate::DafnyType + ::std::default::Default, T19: crate::DafnyType + ::std::default::Default> ::std::default::Default
    for Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    fn default() -> Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
      Tuple20::_T20 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default(),
        _2: ::std::default::Default::default(),
        _3: ::std::default::Default::default(),
        _4: ::std::default::Default::default(),
        _5: ::std::default::Default::default(),
        _6: ::std::default::Default::default(),
        _7: ::std::default::Default::default(),
        _8: ::std::default::Default::default(),
        _9: ::std::default::Default::default(),
        _10: ::std::default::Default::default(),
        _11: ::std::default::Default::default(),
        _12: ::std::default::Default::default(),
        _13: ::std::default::Default::default(),
        _14: ::std::default::Default::default(),
        _15: ::std::default::Default::default(),
        _16: ::std::default::Default::default(),
        _17: ::std::default::Default::default(),
        _18: ::std::default::Default::default(),
        _19: ::std::default::Default::default()
      }
    }
  }

  impl<T0: crate::DafnyType, T1: crate::DafnyType, T2: crate::DafnyType, T3: crate::DafnyType, T4: crate::DafnyType, T5: crate::DafnyType, T6: crate::DafnyType, T7: crate::DafnyType, T8: crate::DafnyType, T9: crate::DafnyType, T10: crate::DafnyType, T11: crate::DafnyType, T12: crate::DafnyType, T13: crate::DafnyType, T14: crate::DafnyType, T15: crate::DafnyType, T16: crate::DafnyType, T17: crate::DafnyType, T18: crate::DafnyType, T19: crate::DafnyType> ::std::convert::AsRef<Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>
    for &Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    fn as_ref(&self) -> Self {
      self
    }
  }
}
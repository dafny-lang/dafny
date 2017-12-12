// RUN: %dafny /env:0 /rprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass<A,B> {
  copredicate P<X,Y>(x: X, y: Y)
  {
    P(x, y)
  }
  copredicate R<T>()
  {
    R<T>()
  }
  static copredicate S<Q>()
  {
    S<Q>()
  }
  static copredicate RST<QQ>()
  {
    MyClass<B,A>.RST<QQ>()
  }
  static copredicate RST_Nat<QQ>[nat]()
  {
    MyClass<B,A>.RST_Nat<QQ>()
  }
  colemma L<U,V>(u: U, v: V)
    ensures P(u, v)
  {
    L(u, v);
  }
  colemma M<W>()
    ensures R<char>()
  {
    M<W>();
    assert R#<char>[_k-1]();
  }
}

colemma N<D0,D1,D2>(o: MyClass<D0,D1>)
  ensures o.R<D2>()
{
  N<D0,D1,D2>(o);
}

colemma O<D0,D1,D2>()
  ensures MyClass<D0,D1>.S<D2>()
{
  O<D0,D1,D2>();
}

colemma {:induction false} RstRst0<alpha,gamma>()
  ensures MyClass<alpha,char>.RST<gamma>()
{  // error: the following is not a proof
  RstRst0<int,gamma>();
}

colemma {:induction false} RstRst1<alpha,gamma>()
  ensures MyClass<alpha,char>.RST<gamma>()
{  // error: the following is not a proof
  RstRst1<int,int>();
}

colemma {:induction false} RstRst2<alpha,gamma>()
  ensures MyClass<alpha,char>.RST<gamma>()
{  // error: the following is not a proof
  RstRst2<alpha,gamma>();
}

colemma {:induction false} RstRst3<alpha,beta,gamma>()
  ensures MyClass<alpha,beta>.RST<gamma>()
{  // error: the following is not a proof
  RstRst3<alpha,beta,gamma>();
}

colemma {:induction false} RstRst4<alpha,beta,gamma>()
  ensures MyClass<alpha,beta>.RST<gamma>()
{
  RstRst4<beta,alpha,gamma>();  // yes
}

colemma {:induction false} RstRst5<alpha,gamma>()
  ensures MyClass<alpha,char>.RST<gamma>()
{
  if 2 <= _k.Offset {
    RstRst5#<alpha,gamma>[_k-2]();  // yes (RST for _k gets unfolded twice)
  } else {  // error: this case does not work out
    assert _k.Offset == 1;
  }
}

colemma {:induction false} RstRst6<alpha,beta,gamma>()
  ensures MyClass<alpha,beta>.RST<gamma>()
{
  if
  case true =>
    // This is the expected and usual proof for all (non-limit) cases
    RstRst6<beta,alpha,gamma>();
  case 2 <= _k.Offset =>
    // here is a "faster" proof
    RstRst6#<alpha,beta,gamma>[_k-2]();  // yes (RST for _k gets unfolded twice)
}

colemma RstRst7<alpha,beta,gamma>()
  ensures MyClass<alpha,beta>.RST<gamma>()
{
  if _k != 1 && _k.Offset == 1 {
    RstRst6<beta,alpha,gamma>();
  } else {
    // in all remaining cases, (unfolding and) automatic induction takes care of the proof
  }
}

colemma {:induction false} RstRst8<alpha,gamma>[nat]()
  ensures MyClass<alpha,char>.RST_Nat<gamma>()
{
  if 2 <= _k {
    RstRst8#<alpha,gamma>[_k-2]();  // yes (RST for _k gets unfolded twice)
  }
}

colemma {:induction false} RstRst9<alpha,beta,gamma>[nat]()
  ensures MyClass<alpha,beta>.RST_Nat<gamma>()
{
  if 2 <= _k {
    RstRst9#<alpha,beta,gamma>[_k-2]();  // yes (RST for _k gets unfolded twice)
  }
}

colemma RstRst10<alpha,beta,gamma>[nat]()
  ensures MyClass<alpha,beta>.RST_Nat<gamma>()
{
  // automatic induction takes care of the proof
}

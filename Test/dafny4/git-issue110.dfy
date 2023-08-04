// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module MyModule {
  export provides MyType, Empty, MyLemma
  type MyType<A>
  ghost function Empty<B>(): MyType<B>
  lemma MyLemma<C>(m: MyType<C>)
    requires m != Empty()  // once upon a time, type inference didn't figure this out
}

// -----------------

module Library {
  export provides MyType, MyFunction

  type MyType<A>
  ghost function MyFunction<B>(q: MyType<B>, b: B): MyType<B>
}

module Client {
  import Library
    // the same bug caused some types not to be filled in, which caused malformed
    // Boogie to be produced
  method Test() {
  }
}

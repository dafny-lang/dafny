// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --type-system-refresh --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Q<K(==)> {
  function put():(r:OM<K>)
}

datatype Getter = Getter {
    function get():(r:Single) {
       Single
    }
}

datatype {:rust_rc false} Option<T> = 
    | None
    | Some(v:T)

datatype Single_ = Single

type Single = t:Single_ | true witness *

type OM<K> = Option<map<K,Single>>

datatype ComplexCase<!K(==,!new)> extends Q<K> = ComplexCase {
    const getter := Getter
    
    function put():(r:OM<K>) {
      var xya := getter.get();
      None
    }
}

method Main() {
  print "ok";
}
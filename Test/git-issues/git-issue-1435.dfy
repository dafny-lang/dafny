// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
	var x:nat;
	twostate predicate p() { unchanged(this) }
	method bad() modifies this ensures false {
		assert p();
		x := x+1;
		assert p();
	}
}

// RUN: %testDafnyForEachResolver "%s"


method foo(xs: set) {
   assert (set x | x in xs) == xs;
}

method bar(xs: iset) {
   assert (iset x | x in xs) == xs;
}

ghost function domain<U, V>(m: map<U,V>): set<U>
   ensures forall i :: i in domain(m) ==> i in m
   ensures forall i :: i in domain(m) <== i in m
{
   set s | s in m
}

ghost function idomain<U, V>(m: imap<U,V>): iset<U>
   ensures forall i :: i in idomain(m) ==> i in m
   ensures forall i :: i in idomain(m) <== i in m
{
   iset s | s in m
}

method foo2(xs: map) {
	  assert (set x | x in xs) == domain(xs);
}

method bar2(xs: imap) {
	  assert (iset x | x in xs) == idomain(xs);
}

// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function domain<U, V>(m: imap<U,V>): set<U>
   // ensures forall i :: i in domain(m) <==> i in m
   ensures forall i :: i in domain(m) ==> i in m
   ensures forall i :: i in domain(m) <== i in m
{
   set s | s in m // UNSAFE, m may have infinite domain
}

ghost function domainAgain<U(!new), V>(m: imap<U,V>): set<U>
   // ensures forall i :: i in domainAgain(m) <==> i in m
   ensures forall i :: i in domainAgain(m) ==> i in m
   ensures forall i :: i in domainAgain(m) <== i in m
{
   set s | s in m // UNSAFE, m may have infinite domain
}

// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


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

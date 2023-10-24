// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Ballot = Ballot(seqno:int)

ghost predicate BalLt(ba:Ballot, bb:Ballot)
{
       ba.seqno < bb.seqno
}

lemma Cases()
{
    var b1:Ballot;
    var b2:Ballot;
    if (b1 == b2) {
    } else if (BalLt(b1,b2)) {
    } else {
        //assert b1.seqno == b1.seqno;
        //assert b2.seqno == b2.seqno;
        assert BalLt(b2, b1); // Fails without asserts above
    }
}
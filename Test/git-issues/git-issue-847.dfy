// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait O {
  var rep:set<O>
  function union<T>(s:set<set<T>>):set<T> {
    set o,o1 | o in s && o1 in o :: o1
  }

  least predicate ag()
    reads *
  {
    rep=={} || (forall o:O | o in rep :: o.ag())
  }

  predicate ldp(n:ORDINAL)
    reads *
  {
    ag#[n]() && (forall n1:ORDINAL | n1 < n:: !ag#[n1]())
  }

  function ld(n:ORDINAL):ORDINAL
    reads *
    requires ag#[n]()
    ensures ldp(ld(n))
  {
    if ldp(n) then n else var n1:ORDINAL :| n1 < n && ag#[n1](); ld(n1)
  }

  function level():ORDINAL
    reads fr()
    requires ag()
    ensures ldp(level())
  {
    var n:ORDINAL :| ag#[n](); ld(n)
  }

  least lemma l1()
    requires ag()
    ensures forall o:O | o in rep :: o.level() < level()
    decreases level()
  {}

  function  fr():set<O>
    requires ag()
    reads *
    decreases level()
  {
    {this} + union(set o:O | o in rep :: l1(); o.fr())
  }
}


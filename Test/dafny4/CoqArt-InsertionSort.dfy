// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Dafny transcription of the Coq development of insertion sort, as found in Coq'Art.

datatype List<T> = Nil | Cons(head: T, tail: List)

predicate sorted(l: List<int>)
{
  match l
  case Nil => true
  case Cons(x, rest) =>
    match rest
    case Nil => true
    case Cons(y, _) => x <= y && sorted(rest)
}

lemma example_sort_2357()
  ensures sorted(Cons(2, Cons(3, Cons(5, Cons(7, Nil)))));
{
}

lemma sorted_inv(z: int, l: List<int>)
  requires sorted(Cons(z, l));
  ensures sorted(l);
{
  match l {
    case Nil =>
    case Cons(_, _) =>
  }
}

// Number of occurrences of z in l
function nb_occ(z: int, l: List<int>): nat
{
  match l
  case Nil => 0
  case Cons(z', l') =>
    (if z == z' then 1 else 0) + nb_occ(z, l')
}

lemma example_nb_occ_0()
  ensures nb_occ(3, Cons(3, Cons(7, Cons(3, Nil)))) == 2;
{
}

lemma example_nb_occ_1()
  ensures nb_occ(36725, Cons(3, Cons(7, Cons(3, Nil)))) == 0;
{
}

// list l' is a permutation of list l
predicate equiv(l: List<int>, l': List<int>)
{
  forall z :: nb_occ(z, l) == nb_occ(z, l')
}

// equiv is an equivalence
lemma equiv_refl(l: List<int>)
  ensures equiv(l, l);
{
}

lemma equiv_sym(l: List<int>, l': List<int>)
  requires equiv(l, l');
  ensures equiv(l', l);
{
}

lemma equiv_trans(l: List<int>, l': List<int>, l'': List<int>)
  requires equiv(l, l') && equiv(l', l'');
  ensures equiv(l, l'');
{
}

lemma equiv_cons(z: int, l: List<int>, l': List<int>)
  requires equiv(l, l');
  ensures equiv(Cons(z, l), Cons(z, l'));
{
}

lemma equiv_perm(a: int, b: int, l: List<int>, l': List<int>)
  requires equiv(l, l');
  ensures equiv(Cons(a, Cons(b, l)), Cons(b, Cons(a, l')));
{
  var L, L' := Cons(a, Cons(b, l)), Cons(b, Cons(a, l'));
  forall z {
    calc {
      nb_occ(z, L);
      (if z == a && z == b then 2 else if z == a || z == b then 1 else 0) + nb_occ(z, l);
      (if z == a && z == b then 2 else if z == a || z == b then 1 else 0) + nb_occ(z, l');
      nb_occ(z, L');
    }
  }
}

// insertion of z into l at the right place (assuming l is sorted)
function method aux(z: int, l: List<int>): List<int>
{
  match l
  case Nil => Cons(z, Nil)
  case Cons(a, l') =>
    if z <= a then Cons(z, l) else Cons(a, aux(z, l'))
}

lemma example_aux_0()
  ensures aux(4, Cons(2, Cons(5, Nil))) == Cons(2, Cons(4, Cons(5, Nil)));
{
}

lemma example_aux_1()
  ensures aux(4, Cons(24, Cons(50, Nil))) == Cons(4, Cons(24, Cons(50, Nil)));
{
}

// the aux function seems to be a good tool for sorting...

lemma aux_equiv(l: List<int>, x: int)
  ensures equiv(Cons(x, l), aux(x, l));
{
  match l {
    case Nil =>
    case Cons(_, _) =>
  }
}

lemma aux_sorted(l: List<int>, x: int)
  requires sorted(l);
  ensures sorted(aux(x, l));
{
  match l {
    case Nil =>
    case Cons(_, l') =>
      match l' {
        case Nil =>
        case Cons(_, _) =>
      }
  }
}

// the sorting function
function sort(l: List<int>): List<int>
  ensures var l' := sort(l); equiv(l, l') && sorted(l');
{
  existence_proof(l);
  var l' :| equiv(l, l') && sorted(l'); l'
}

lemma existence_proof(l: List<int>)
  ensures exists l' :: equiv(l, l') && sorted(l');
{
  match l {
    case Nil =>
      assert sorted(Nil);
    case Cons(x, m) =>
      existence_proof(m);
      var m' :| equiv(m, m') && sorted(m');
      calc ==> {
        equiv(m, m') && sorted(m');
        equiv(l, Cons(x, m')) && sorted(m');
        { aux_equiv(m', x); }
        equiv(l, aux(x, m')) && sorted(m');
        { aux_sorted(m', x); }
        equiv(l, aux(x, m')) && sorted(aux(x, m'));
      }
  }
}

// to get a compilable function in Dafny
function method Sort(l: List<int>): List<int>
  ensures equiv(l, Sort(l)) && sorted(Sort(l));
{
  match l
  case Nil => l
  case Cons(x, m) =>
    var m' := Sort(m);
    assert equiv(l, Cons(x, m'));
    aux_equiv(m', x);
    aux_sorted(m', x);
    aux(x, m')
}

predicate p_aux_equiv(l: List<int>, x: int)
  ensures equiv(Cons(x, l), aux(x, l));
{
  aux_equiv(l, x);
  true
}

predicate p_aux_sorted(l: List<int>, x: int)
  requires sorted(l);
  ensures sorted(aux(x, l));
{
  aux_sorted(l, x);
  true
}

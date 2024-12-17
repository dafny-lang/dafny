// RUN: %verify --allow-axioms --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Pos = x | 0 < x witness 1

/** Matrix dimension */
const N : Pos

/** Matrix indices */
type Index = x | 0 <= x < N      // matrix indices

type Matrix = Index -> Index -> int

/** Function extensionality */
lemma FunEq<X, Y>(f: X -> Y, g: X -> Y)
  requires forall x :: f(x) == g(x)
  ensures f == g
{
  assume false;
}

lemma Same(a: Matrix, b: Matrix)
  requires forall x: Index, y: Index :: a(x)(y) == b(x)(y)
  ensures a == b
{
  forall x: Index
    ensures a(x) == b(x)
  {
    FunEq(a(x), b(x));
  }
  FunEq(a, b);
}

/** Σ f(i) where i ranges from 0 to less than n */
function Sum_n(f: Index -> int, n: nat): int
  requires n <= N
{
  if n == 0 then 0 else f(n - 1) + Sum_n(f, n - 1)
}

/** Σ f(i) where i ranges from 0 to less than N */
function Sum(f: Index -> int): int {
  Sum_n(f, N)
}

/** Matrix multiplication */
function mult(a: Matrix, b: Matrix): Matrix
{
  ((x: Index) => (y: Index) =>
    Sum((k: Index) => a(x)(k) * b(k)(y)))
}

/** Σ f  +  Σ g  == Σ (i => f(i) + g(i)) */
/** proof by induction */
lemma distr_add_n(f: Index -> int, g: Index -> int, n: nat)
  requires n <= N
  ensures Sum_n(f, n) + Sum_n(g, n) == Sum_n((i: Index) => f(i) + g(i), n)
{}

/** (Σ f) * x == Σ (i => f(i) * x) */
/** proof by induction */
lemma {:induction n} distr_mult_n(f: Index -> int, n: nat, x: int)
  requires n <= N
  ensures Sum_n(f, n) * x == Sum_n((i: Index) => f(i) * x, n)
{}

/** (Σ f) * x == Σ (i => f(i) * x) */
lemma distr_mult(f: Index -> int, x: int)
  ensures Sum(f) * x == Sum((i: Index) => f(i) * x)
{
  distr_mult_n(f, N, x);
}

/** Σ_k (Σ_l f(k,l))  ==  Σ_l (Σ_k f(k,l)) */
/** proof by induction */
lemma {:induction m, n1, n2} {:nowarn} sum_assoc_n(m: Matrix, n1: nat, n2: nat)
  requires n1 <= N && n2 <= N
  ensures Sum_n((k: Index) => Sum_n((l: Index) => m(k)(l), n1), n2)
          ==
          Sum_n((l: Index) => Sum_n((k: Index) => m(k)(l), n2), n1)
{
  var f  := (k: Index) => Sum_n((l: Index) => m(k)(l), n1);
  var g  := (l: Index) => Sum_n((k: Index) => m(k)(l), n2);
  if n2 == 0 {
    calc {
        Sum_n(f, n2);
    ==
        0;
    ==
        Sum_n(g, n2);
    }
  } else {
    var f2 := (l: Index) => m(n2 - 1)(l);
    var g2 := (l: Index) => Sum_n((k: Index) => m(k)(l), n2 - 1);
    calc {
        Sum_n(f, n2);
    == // def of Sum_n
        f(n2 - 1) + Sum_n(f, n2 - 1);
    == // beta reduction
        Sum_n(f2, n1) + Sum_n(f, n2 - 1);
    == // IH applied to Sum_n(f, n2 - 1)
        Sum_n(f2, n1) + Sum_n(g2, n1);
    == { distr_add_n(f2, g2, n1); }
        Sum_n((l: Index) => f2(l) + g2(l), n1);
    == { // substituting f2 and g2
        FunEq((l: Index) => f2(l) + g2(l),
                (l: Index) => m(n2 - 1)(l) + Sum_n((k: Index) => m(k)(l), n2 - 1)); }
        Sum_n((l: Index) => m(n2 - 1)(l) + Sum_n((k: Index) => m(k)(l), n2 - 1), n1);
    == { FunEq((l: Index) => m(n2 - 1)(l) + Sum_n((k: Index) => m(k)(l), n2 - 1),
               (l: Index) => Sum_n((k: Index) => m(k)(l), n2)); }
        Sum_n((l: Index) => Sum_n((k: Index) => m(k)(l), n2), n1);
    }
  }
}

/** Σ_k (Σ_l f(k,l))  ==  Σ_l (Σ_k f(k,l)) */
lemma sum_assoc(m: Matrix)
  ensures Sum((k: Index) => Sum((l: Index) => m(k)(l)))
          ==
          Sum((l: Index) => Sum((k: Index) => m(k)(l)))
{
  calc {
      Sum((k: Index) => Sum((l: Index) => m(k)(l)));
  == { FunEq((k: Index) => Sum((l: Index) => m(k)(l)),
             (k: Index) => Sum_n((l: Index) => m(k)(l), N)); }
      Sum_n((k: Index) => Sum_n((l: Index) => m(k)(l), N), N);
  == { sum_assoc_n(m, N, N); }
      Sum_n((l: Index) => Sum_n((k: Index) => m(k)(l), N), N);
  == { FunEq((l: Index) => Sum((k: Index) => m(k)(l)),
             (l: Index) => Sum_n((k: Index) => m(k)(l), N)); }
      Sum((l: Index) => Sum((k: Index) => m(k)(l)));
  }
}

/** Σ_k (Σ_l (a * b * c))  ==  Σ_l (Σ_k (a * b * c)) */
lemma sum_assoc_mult(a: Matrix, b: Matrix, c: Matrix, i: Index, j: Index)
  ensures Sum((k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j)))
          ==
          Sum((l: Index) => Sum((k: Index) => a(i)(l) * b(l)(k) * c(k)(j)))
{
  var m := (k1: Index) => (l1: Index) => a(i)(l1) * b(l1)(k1) * c(k1)(j);
  calc {
      Sum((k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j)));
  == {
      forall k: Index
          ensures ((l: Index) => a(i)(l) * b(l)(k) * c(k)(j))
                  ==
                  ((l: Index) => m(k)(l))
      { FunEq((l: Index) => a(i)(l) * b(l)(k) * c(k)(j),
              (l: Index) => m(k)(l)); }
      FunEq((k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j)),
            (k: Index) => Sum((l: Index) => m(k)(l))); }
      Sum((k: Index) => Sum((l: Index) => m(k)(l)));
  == { sum_assoc(m); }
      Sum((l: Index) => Sum((k: Index) => m(k)(l)));
  == {
          forall l: Index
              ensures ((k: Index) => m(k)(l))
                      ==
                      ((k: Index) => a(i)(l) * b(l)(k) * c(k)(j))
          {
              FunEq((k: Index) => m(k)(l),
                    (k: Index) => a(i)(l) * b(l)(k) * c(k)(j));
          }
          FunEq((l: Index) => Sum((k: Index) => m(k)(l)),
                (l: Index) => Sum((k: Index) => a(i)(l) * b(l)(k) * c(k)(j)));
      }
      Sum((l: Index) => Sum((k: Index) => a(i)(l) * b(l)(k) * c(k)(j)));
  }
}

/** (a * (b * c))(i, j) == ((a * b) * c)(i, j) */
lemma {:isolate_assertions} mult_assoc_ij(a: Matrix, b: Matrix, c: Matrix, i: Index, j: Index)
  ensures mult(mult(a, b), c)(i)(j) == mult(a, mult(b, c))(i)(j)
{
  calc {
      mult(mult(a, b), c)(i)(j);
  ==
      Sum((k: Index) => mult(a, b)(i)(k) * c(k)(j));
  == { assert forall k : Index :: mult(a, b)(i)(k) == Sum((l: Index) => a(i)(l) * b(l)(k));
       FunEq((k: Index) => mult(a, b)(i)(k) * c(k)(j),
             (k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k)) * c(k)(j)); }
      Sum((k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k)) * c(k)(j));
  == {
          forall k: Index
              ensures Sum((l: Index) => a(i)(l) * b(l)(k)) * c(k)(j)
                      ==
                      Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j))
          {
              var g := (l: Index) => a(i)(l) * b(l)(k);
              var x := c(k)(j);
              calc {
                  Sum((l: Index) => a(i)(l) * b(l)(k)) * c(k)(j);
              ==
                  Sum(g) * x;
              == { distr_mult(g, x); }
                  Sum((l: Index) => g(l) * x);
              == { FunEq((l: Index) => g(l) * x,
                         (l: Index) => a(i)(l) * b(l)(k) * c(k)(j)); }
                  Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j));
              }
          }
          FunEq((k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k)) * c(k)(j),
                (k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j)));
         }
      Sum((k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j)));
  == { sum_assoc_mult(a, b, c, i, j); }
      Sum((l: Index) => Sum((k: Index) => a(i)(l) * b(l)(k) * c(k)(j)));
  == // alpha-renaming k <-> l
      Sum((k: Index) => Sum((l: Index) => a(i)(k) * b(k)(l) * c(l)(j)));
  == {
          forall k: Index
              ensures Sum((l: Index) => a(i)(k) * b(k)(l) * c(l)(j))
                      ==
                      Sum((l: Index) => b(k)(l) * c(l)(j) * a(i)(k))
          {
              FunEq((l: Index) => a(i)(k) * b(k)(l) * c(l)(j),
                    (l: Index) => b(k)(l) * c(l)(j) * a(i)(k));
          }
          FunEq((k: Index) => Sum((l: Index) => a(i)(k) * b(k)(l) * c(l)(j)),
                (k: Index) => Sum((l: Index) => b(k)(l) * c(l)(j) * a(i)(k)));
      }
      Sum((k: Index) => Sum((l: Index) => b(k)(l) * c(l)(j) * a(i)(k)));
  == {
          forall k: Index
              ensures Sum((l: Index) => b(k)(l) * c(l)(j)) * a(i)(k)
                      ==
                      Sum((l: Index) => b(k)(l) * c(l)(j) * a(i)(k))
          {
              var g := (l: Index) => b(k)(l) * c(l)(j);
              var x := a(i)(k);
              calc {
                  Sum((l: Index) => b(k)(l) * c(l)(j)) * a(i)(k);
              ==
                  Sum(g) * x;
              == { distr_mult(g, x); }
                  Sum((l: Index) => g(l) * x);
              == { FunEq((l: Index) => g(l) * x,
                             (l: Index) => b(k)(l) * c(l)(j) * a(i)(k)); }
                  Sum((l: Index) => b(k)(l) * c(l)(j) * a(i)(k));
              }
          }
          FunEq((k: Index) => Sum((l: Index) => b(k)(l) * c(l)(j) * a(i)(k)),
                (k: Index) => Sum((l: Index) => b(k)(l) * c(l)(j)) * a(i)(k));
      }
      Sum((k: Index) => Sum((l: Index) => b(k)(l) * c(l)(j)) * a(i)(k));
  == { FunEq((k: Index) => Sum((l: Index) => b(k)(l) * c(l)(j)) * a(i)(k),
             (k: Index) => a(i)(k) * Sum((l: Index) => b(k)(l) * c(l)(j))); }
      Sum((k: Index) => a(i)(k) * Sum((l: Index) => b(k)(l) * c(l)(j)));
  == { FunEq((k: Index) => a(i)(k) * Sum((l: Index) => b(k)(l) * c(l)(j)),
             (k: Index) => a(i)(k) * mult(b, c)(k)(j)); }
      Sum((k: Index) => a(i)(k) * mult(b, c)(k)(j));
  ==
      mult(a, mult(b, c))(i)(j);
  }
}

/** a * (b * c) == (a * b) * c */
lemma mult_assoc(a: Matrix, b: Matrix, c: Matrix)
  ensures mult(mult(a, b), c) == mult(a, mult(b, c))
{
  forall i: Index, j: Index
    ensures mult(mult(a, b), c)(i)(j) == mult(a, mult(b, c))(i)(j)
  {
    mult_assoc_ij(a, b, c, i, j);
  }
  Same(mult(mult(a, b), c), mult(a, mult(b, c)));
}

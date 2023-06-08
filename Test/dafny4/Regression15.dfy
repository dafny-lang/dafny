// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var b;
  b := M0();  print b, "\n";
  b := M1();  print b, "\n";
  b := M2();  print b, "\n";
  b := M3();  print b, "\n";
  b := M4();  print b, "\n";
  Sets();
  Orderings();
  SubSets();
}

method M0() returns (b: bool) {
//  b := forall i, j | j <= i <= 100 && i <= j < 100 :: true;  // see dafny0/ResolutionErrors.dfy
}

predicate F(i: int, j: int) { true }

method M1() returns (b: bool) {
  b := forall i,j :: 0 <= i < 100 && i-1 <= j < i+2 ==> F(i,j);
}

method M2() returns (b: bool) {
  b := forall j,i :: 0 <= i < 100 && i-1 <= j < i+2 ==> F(i,j);
}

function S(i: int): set<int> { {i} }

method M3() returns (b: bool) {
  b := forall i,j :: 0 <= i < 100 && j in S(i) ==> F(i,j);
}

method M4() returns (b: bool) {
//  b := forall i, j :: j <= i < 100 && j in S(i) ==> F(i,j);  // see dafny0/ResolutionErrors.dfy
}

function Triple(i: int, j: int, k: int): int
{
  100*i + 10*j + k
}

method Sets()
{
  print set i,j,k | 4 <= i+2 <= j+3 <= k+4 <= 7 :: Triple(i, j, k), "\n";
  print set i,k,j | 4 <= i+2 <= j+3 <= k+4 <= 7 :: Triple(i, j, k), "\n";
  print set j,i,k | 4 <= i+2 <= j+3 <= k+4 <= 7 :: Triple(i, j, k), "\n";
  print set k,i,j | 4 <= i+2 <= j+3 <= k+4 <= 7 :: Triple(i, j, k), "\n";
  print set j,k,i | 4 <= i+2 <= j+3 <= k+4 <= 7 :: Triple(i, j, k), "\n";
  print set k,j,i | 4 <= i+2 <= j+3 <= k+4 <= 7 :: Triple(i, j, k), "\n";
}

// -----

method Orderings() {
  var h := MethodA({{57,59},{20,18}}, {59});
  print h, "\n";
}
function Xit(X: set, Y: set): set { X }
method MethodA<G>(f: set<set<G>>, M: set<G>) returns (h: set<set<G>>) {
  h := set Y,X | Y in f && X <= Y && M + X == Y :: Xit(X, Y);
}

// -----

method SubSets() {
  var h := PA({{57,59},{20,18}}, {59});
  print h, "\n";
  h := PA({{57,59},{20,18}}, {20});
  print h, "\n";
  var b := PB({{57,59},{20,18}}, {59});
  print b, "\n";
}
method PA<G>(f: set<set<G>>, M: set<G>) returns (h: set<set<G>>) {
  h := set X,Y | Y in f && X <= Y && M + X == Y :: Xit(X,Y);
}
predicate PS(X: set, Y: set) { X <= Y }
method PB<G>(f: set<set<G>>, M: set<G>) returns (h: bool) {
  h := forall Y,X | Y in f && X <= Y && M + X == Y :: PS(X, Y);
}

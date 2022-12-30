// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Simple(m: map<int, real>, n: map<int, real>, s: set<int>) returns (r: map<int, real>)
{
  if
  case true =>
    var tmp := m + n - s;
    r := tmp;
  case true =>
    var tmp := m - s + n;
    r := tmp;
  case true =>
    var tmp := m + (n - s);
    r := tmp;
}

method SimpleI(m: imap<int, real>, n: imap<int, real>, s: set<int>) returns (r: imap<int, real>)
{
  if
  case true =>
    var tmp := m + n - s;
    r := tmp;
  case true =>
    var tmp := m - s + n;
    r := tmp;
  case true =>
    var tmp := m + (n - s);
    r := tmp;
}

method MismatchedRangeTypes(m: map<int, real>, n: map<int, bool>, s: set<int>)
{
  if
  case true =>
    var r := m + n - s;  // error: cannot union map<int, real> and map<int, bool>
  case true =>
    var r := m - s + n;  // error: cannot union map<int, real> and map<int, bool>
  case true =>
    var r := m + (n - s);  // error: cannot union map<int, real> and map<int, bool>
}

method MismatchedDomainTypes(m: map<int, real>, n: map<bool, real>, s: set<int>)
{
  if
  case true =>
    var r := m + n;  // error: cannot union map<int, real> and map<bool, real>
  case true =>
    var r := m - s + n;  // error: cannot union map<int, real> and map<bool, real>
  case true =>
    var r := n - s;  // error: cannot subtract set<int> from map<bool, real>
}

// alas, subtracting an iset is not supported, even from an imap
method UnsupportedSubtract(m: map<int, real>, n: imap<int, real>, s: set<int>, t: iset<int>) returns (g: map<int, real>, h: imap<int, real>)
{
  if
  case true =>
    var r := m - s;
    g := r;
  case true =>
    var r := n - s;
    h := r;
  case true =>
    var r := m - t;  // error: map subtraction expects t to have type set<int>
  case true =>
    var r := n - t;  // error: map subtraction expects t to have type set<int>
}

// alas, whether or not a '-' is deemed to be a map subtraction is determined by
// what is known when type checking first reaches the operator
method TooEagerResolution(m: map<int, real>, n: map<int, real>, s: set<int>)
{
  // all fine here:
  var a, b;
  var r := a + b;
  a, b := m, n;

  // here, we see a consequence of the eager operator selection:
  var g, t;
  // since it's not yet known that g is a map, the next line will resolve to any '-' other than
  // map subtraction
  var r1 := g - t;  // this picks the wrong '-'
  g, t := m, s;  // error: the error is reported here
}

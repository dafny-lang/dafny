// RUN: %exits-with 4 %dafny /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Issues(a: bool, s: set) {
  // Each one of the following 8 calc statements used to cause a crash

  if
  case true =>
    calc { a; <== false; }
  case true =>
    calc { true; <== a; }
  case true =>
    calc { a; ==> true; }
  case true =>
    calc { false; ==> a; }

  case true =>
    calc { s; >= ({}); }
  case true =>
    calc { s; > ({}); } // error: cannot prove calc step
  case true =>
    calc { {}; <= s; }
  case true =>
    calc { {}; < s; } // error: cannot prove calc step
}

// NONUNIFORM: Javascript-specific extern test
// RUN: %run --unicode-char false --target js "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// "url" is a built-in package in node, so it should be accessible to the
// test suite without further requirements on the setup.
module {:extern "url", "url"} URL {
  class Url {
    var host: string
    var pathname: string
    var search: string
  }
  // Note that passing a Dafny string directly as a JS string only works in --unicode-char false mode
  method {:axiom} {:extern "parse"} Parse(address: string, b: bool) returns (u: Url)
}

method Main() {
  var address := "http://localhost:8080/default.htm?year=1915&month=august&day=29";
  var u := URL.Parse(address, true);
  print "The address ", address, "\n";
  print "has the following parts:\n";
  print "host: ", u.host, "\n";
  print "pathname: ", u.pathname, "\n";
  print "search: ", u.search, "\n";
}

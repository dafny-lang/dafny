/*
---
!dafnyTestSpec
dafnyArguments:
    compileTarget: js
*/

// "url" is a built-in package in node, so it should be accessible to the
// test suite without further requirements on the setup.
module {:extern "url", "url"} URL {
  class Url {
    var host: string
    var pathname: string
    var search: string
  }
  method {:extern "parse"} Parse(address: string, b: bool) returns (u: Url)
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

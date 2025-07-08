// NONUNIFORM: Go-specific extern test
// RUN: %exits-with 3 %run --allow-external-contracts --target go "%s" &> "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: undefined: m_GoModuleConversions.ParseURL

// This test used to work only because of a questionable Go-only feature
// of mapping a Dafny string directly to a Go string when passed in or out of
// an extern method. It barely worked in one direction and not in the other
// (see https://github.com/dafny-lang/dafny/issues/2989),
// and even when it did, equating these two types was not actually sound in all cases anyway.
// This feature has been disabled since Dafny 4.0,
// and unfortunately I found that rewriting the test to work without it was very
// difficult for unrelated reasons.
// In particular this version should work but produces unused imports
// which the Go compiler complains about
// (see https://github.com/dafny-lang/dafny/issues/2953).
// Instead I've converted this into a negative test.

// "url" is a built-in package, so it should be accessible to the
// test suite without further requirements on the setup.
module {:extern "url", "net/url"} {:dummyImportMember "URL", true} URL {

  class URL {
    var {:extern "Host"} host: string
    var {:extern "Path"} pathname: string
    var {:extern "RawQuery"} search: string
  }

  trait {:extern "", "error"} Error extends object { }
}

module {:extern "GoModuleConversions"} {:dummyImportMember "ParseURL", false} GoModuleConversions {
  import opened URL
  method {:extern "ParseURL"} Parse(address: string) returns (url: URL, error: Error?)
}

module Test {

  import GoModuleConversions

  method TryUrl(address: string) {
    var u, e := GoModuleConversions.Parse(address);
    if (e != null) {
      print "Parse error: ", e, "\n";
    } else {
      print "The address ", address, "\n";
      print "has the following parts:\n";
      print "host: ", u.host, "\n";
      print "pathname: ", u.pathname, "\n";
      print "search: ", u.search, "\n";
    }
  }

  method Main() {
    TryUrl("http://localhost:8080/default.htm?year=1915&month=august&day=29");
    TryUrl("http://localhost:8080/default.htm%");
  }
}

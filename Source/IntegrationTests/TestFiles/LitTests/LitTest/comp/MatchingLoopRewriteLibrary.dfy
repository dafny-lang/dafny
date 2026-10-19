// RUN: %dafny /compileTarget:cs /useRuntimeLib /out:%S/Output/MatchingLoopRewriteLib.dll %S/Inputs/MatchingLoopRewriteLib.dfy > "%t"
// RUN: %dafny /compile:0 "%s" %S/Output/MatchingLoopRewriteLib.dll >> "%t"
// RUN: %diff "%s.expect" "%t"

// The library's assembly embeds the library's Dafny source, which Dafny resolves again here. It has no trigger that
// needs a term that the trigger generator named, so Dafny selects the triggers again.
module Client {
  import Library

  method Test(s: seq<int>)
    requires Library.Sorted(s) && |s| > 2
  {
    assert s[0] <= s[1];
  }
}

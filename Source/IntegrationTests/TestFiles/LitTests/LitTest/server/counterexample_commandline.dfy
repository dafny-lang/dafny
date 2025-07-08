
// RUN: %exits-with 4 %verify --extract-counterexample "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The following method performs string equality comparison whereas its 
// specification states that it must perform pattern matching (the difference
// being that the '?' metacharacter in the pattern is supposed to match
// any character in the string). 
module Patterns {

    class Simple {

        var p:string

        method Match(s: string) returns (b: bool) 
            requires |p| == 1 // this is to make counterexample deterministic
            requires |p| == |s|
            ensures b <==> forall n :: 0 <= n < |s| ==> 
                    s[n] == p[n] || 
                    p[n] == '?'
        { 
            b := false;
            var i := 0;
            while (i < |s|) 
                invariant i <= |s|
                invariant forall n :: 0 <= n < i ==> 
                    s[n] == p[n] || 
                    p[n] == '?'
            {
                if (s[i] != p[i]) { // must add && (p[i] != '?') to verify
                    return;
                } 
                i := i + 1;
            }
            return true;
        }
    }

}

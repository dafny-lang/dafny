// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The let bindings for each `p` must be inlined before trigger selection
// on the nested map comprehension, otherwise the selected trigger will be
// invalid

function Rewrite(env: map<nat, nat>): map<nat, nat> {
    var p := map n: nat | n in env :: n;
    map n: nat | n in p :: n
}

function Rewrite2(strs: set<string>): map<string, string> {
    var p := map s: string | s in strs :: s;
    map s: string | s in p :: s
}
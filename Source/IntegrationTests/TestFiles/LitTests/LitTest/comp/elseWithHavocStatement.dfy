// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

method Main() {
    var b: bool :| true; 
    var r: int;
    if b {
      r := 13;
    } else {
      r := *;
    }
    print r;
}
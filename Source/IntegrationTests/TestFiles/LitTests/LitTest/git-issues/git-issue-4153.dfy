// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" 

codatatype NameclashCo = CoCtor(x: int)
{
  method Get() returns (u: int) { return 79; }
}


method Main() {
    print "Hello!\n";
}


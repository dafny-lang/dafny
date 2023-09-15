// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment

method Main() {
    var c := 1;
    print(c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c
          + c + c + c + c + c + c + c), "\n";
}


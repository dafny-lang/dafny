// RUN: %testDafnyForEachResolver "%s" -- --skip-included-files


include "git-issue64.dfyi"

ghost function id(x:word): word { x }

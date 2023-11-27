// RUN: %testDafnyForEachResolver "%s"


include "git-issue64.dfyi"

ghost function id(x:word): word { x }

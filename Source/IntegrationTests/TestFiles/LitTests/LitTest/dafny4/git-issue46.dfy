// RUN: %testDafnyForEachResolver "%s" -- --skip-included-files


include "git-issue46-include.dfyi"

module m4 refines m2 { }



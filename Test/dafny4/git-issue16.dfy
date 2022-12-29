// RUN: %exits-with 2 %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "git-issue16.dfyi"

lemma UhOh()
  ensures false
{
}

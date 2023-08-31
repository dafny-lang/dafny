// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


include "git-issue16.dfyi"

lemma UhOh()
  ensures false
{
}

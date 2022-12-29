// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M()
  modifies set o: object | true
{
}

method Client()
{
  assume forall o: object {:nowarn} :: false;
  M();
}

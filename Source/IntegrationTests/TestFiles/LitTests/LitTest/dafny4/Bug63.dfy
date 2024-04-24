// RUN: %testDafnyForEachResolver "%s" -- --allow-warnings


method M()
  modifies set o: object | true
{
}

method Client()
{
  assume forall o: object {:nowarn} :: false;
  M();
}

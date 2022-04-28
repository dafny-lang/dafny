DafnyRuntime.Helpers.Print(new BigInteger(1));
DafnyRuntime.Helpers.Print("A");
DafnyRuntime.Helpers.Print(DafnyRuntime.Sequence<>.FromElements(new BigInteger(1), (new BigInteger(2) + new BigInteger(3)), new BigInteger(4)));
if ((true && false)) {
  DafnyRuntime.Helpers.Print("true");
} else {
  DafnyRuntime.Helpers.Print("false");
}

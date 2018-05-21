method m()
{
   assert forall a: seq<int>, b: seq<int>, c: seq<int> ::
      (a + b) + c == a + (b + c);
}
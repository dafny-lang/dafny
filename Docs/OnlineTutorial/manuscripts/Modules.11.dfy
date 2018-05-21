module Implementation {
  static function method addSome(n: nat): nat 
    ensures addSome(n) == n + 1;
  {
    n + 1
  }
}
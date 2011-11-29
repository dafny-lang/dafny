// ---------------------- chaining operators -----------------------------------

method TestChaining0(j: int, k: int, m: int)
  requires j != k != m;  // error: cannot have more than one != per chain
  requires j == k == m;  // dandy
  requires j < k == m == m+1 != m+2 >= 100;  // error: cannot mix < and >=
  requires j >= k == m == m-1 != m-2 < 100;  // error: cannot mix >= and <
{
}

method TestChaining1<T>(s: set<T>, t: set<T>, u: set<T>, x: T, SuperSet: set<set<T>>)
  requires s <= t <= u >= s+u;  // error: cannot mix <= and >=
  ensures s <= u;
  ensures s !! t !! u; // valid, means pairwise disjoint
  ensures x in s in SuperSet;  // error: 'in' is not chaining
  ensures x !in s in SuperSet;  // error: 'in' is not chaining
  ensures x in s !in SuperSet;  // error: 'in' is not chaining
  ensures x in s == t;  // error: 'in' is not chaining
{
}

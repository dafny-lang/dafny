method test()
{
   assert multiset([1,1]) == multiset{1,1};
   assert multiset({1,1}) == multiset{1};
}
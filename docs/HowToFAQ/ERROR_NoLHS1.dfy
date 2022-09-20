method PickKey<K, V>(m: map<K, V>) returns (ret: K) 
  requires |m.Keys| > 0
{
  var k :| k in m;
  return k;
}

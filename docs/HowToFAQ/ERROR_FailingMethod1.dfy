method RemoveKey<K, V>(m: map<K, V>, k: K) returns (ret: map<K, V>)
  requires m.Keys != {} && k in m
  ensures k !in ret
{
  return map k' | k' in m && k' != k :: m[k'];
}

while m'.Keys != {} {
  var k :| k in m';
  m' := RemoveKey(m', k);
}

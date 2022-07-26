method test(m: map<int,int>) {
  var m' := m;
  ghost var gm := m';
  while m'.Keys != {} 
    invariant m'.Keys <= m.Keys 
    decreases |m'.Keys|
  {
    gm := m';
    var k :| k in m';
    m' := map k' | k' in m' && k' != k :: m'[k'];
    assert m'.Keys <= gm.Keys 
  }
}

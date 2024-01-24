// RUN: ! %verify --filter-position='filter.dfy' %s > %t
// RUN: ! %verify --filter-position='filter.dfy:12' %s >> %t
// RUN: ! %verify --filter-position='src/source1.dfy:5' %S/Input/dfyconfig.toml >> %t
// RUN: %verify --filter-position='src/source1.dfy:2' %S/Input/dfyconfig.toml >> %t
// RUN: %diff "%s.expect" "%t"

method Succeeds()
  ensures true {
}

method Fails() 
  ensures false {
}

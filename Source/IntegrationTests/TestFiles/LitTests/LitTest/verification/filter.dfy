// RUN: %verify --filter-position='blaergaerga' %s > %t
// RUN: %verify --filter-position='C:\windows\path.dfy' %s >> %t
// RUN: ! %verify --filter-position='filter.dfy' %s >> %t
// RUN: ! %verify --filter-position='filter.dfy:14' %s >> %t
// RUN: ! %verify --filter-position='src/source1.dfy:5' %S/Inputs/dfyconfig.toml >> %t
// RUN: %verify --filter-position='src/source1.dfy:2' %S/Inputs/dfyconfig.toml >> %t
// RUN: %diff "%s.expect" "%t"

method Succeeds()
  ensures true {
}

method Fails() 
  ensures false {
}

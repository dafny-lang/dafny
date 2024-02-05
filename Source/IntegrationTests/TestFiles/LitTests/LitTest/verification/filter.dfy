// RUN: %verify --filter-position='C:\windows\path.dfy' %s > %t
// RUN: ! %verify --filter-position='src/source1.dfy:5' %S/Inputs/dfyconfig.toml >> %t
// RUN: %verify --filter-position='src/source1.dfy:1' %S/Inputs/dfyconfig.toml >> %t
// RUN: ! %verify --filter-position='e.dfy' %S/inputs/single-file.dfy >> %t
// RUN: %verify --filter-position='e.dfy:2' %S/inputs/single-file.dfy >> %t
// RUN: %verify --filter-position='blaergaerga' %S/inputs/single-file.dfy >> %t
// RUN: ! %verify --isolate-assertions --filter-position='e.dfy:5' %S/inputs/single-file.dfy >> %t
// RUN: %verify --isolate-assertions --filter-position='e.dfy:6' %S/inputs/single-file.dfy >> %t
// RUN: %verify --isolate-assertions --filter-position='e.dfy:7' %S/inputs/single-file.dfy >> %t
// RUN: ! %verify --isolate-assertions --filter-position='e.dfy:8' %S/inputs/single-file.dfy >> %t
// RUN: %verify --isolate-assertions --filter-position='e.dfy:9' %S/inputs/single-file.dfy >> %t
// RUN: ! %verify --isolate-assertions --filter-position='e.dfy:16' %S/inputs/single-file.dfy >> %t
// RUN: %verify --isolate-assertions --filter-position='e.dfy:20' %S/inputs/single-file.dfy >> %t
// RUN: %diff "%s.expect" "%t"
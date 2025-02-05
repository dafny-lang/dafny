// RUN: ! %verify --input-format Binary %S/Input/assertTrue.dbin > %t
// RUN: %diff "%s.expect" "%t"

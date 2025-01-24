// RUN: %verify --filter-symbol='blaergaerga' %s > %t
// RUN: ! %verify --filter-symbol='P' %s >> %t
// RUN: ! %verify --filter-symbol='Q' %s >> %t
// RUN: ! %verify --filter-symbol='P.Q' %s >> %t
// RUN: ! %verify --filter-symbol='Q.P' %s >> %t
// RUN: ! %verify --filter-symbol='DT' %s >> %t
// RUN: ! %verify --filter-symbol='R1' %s >> %t
// RUN: %diff "%s.expect" "%t"

module P {
  module Q {
    method A() ensures false {}
  }
  method B() ensures false {}
}

module Q {
  module P {
    method C() ensures false {}
  }
  method D() ensures false {}
}

method E() ensures false {}

datatype DT = R1(x: nat := -1) | R2(y: nat := -1)


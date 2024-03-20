// RUN: echo Used in WithInclude.dfy test

module Library {
  method Kaboom() {
    print 1/0;
  }
}

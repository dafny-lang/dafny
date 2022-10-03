// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1 {

  datatype D1 = C1(D2)

  datatype D2 = C2 | C3(D1)

}

module M2 {
	
  import M1

  datatype D3 = C4(M1.D1)
}

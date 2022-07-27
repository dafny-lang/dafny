module M {
  export provides String
  datatype String = String(str: string)
}

module A {
  import opened M
  method test() {
    var s := String("");
  }
}

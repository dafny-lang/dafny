import A = B;
method m() {
  A.whatever();
}
module B {
  static method whatever() {}
}
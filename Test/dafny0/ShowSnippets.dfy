// There is a known bug in this feature where it can't find the original file if
// /useBaseNameForFileName is used and the file isn't in the current directory:
// https://github.com/dafny-lang/dafny/issues/1518.
// To work around this, we don't pass /useBaseNameForFileName and instead manually
// truncate the source paths to their base names using sed.
// RUN: %exits-with 4 %baredafny /compile:0 /showSnippets:1 "%s" > "%t".raw
// RUN: %sed 's/^.*[\/\\]//' "%t".raw > "%t"
// RUN: %diff "%s.expect" "%t"

method Never() requires true && false {}

method Test1() {
  assert false;
}

method Test2() {
  Never();
}

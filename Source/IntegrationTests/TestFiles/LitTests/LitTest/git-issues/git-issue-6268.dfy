// RUN: %exits-with 134 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Color = Red | Blue

method Test(color: Color)
{
  match color
  case Red =>
    assert L: true;
    reveal L;
  case Blue =>
}

// RUN: %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m()
  ensures false
{
}

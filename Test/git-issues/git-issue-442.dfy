// RUN: %dafny /noVerify /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() 
  ensures false
{
}

// RUN: %verify %s > %t
// RUN: %diff "%s.expect" "%t"

function Crash(e: nat): string
{
  assert match e { case _ => true };
  ""
}
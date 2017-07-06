method M() returns (ok: bool)
  ensures ok
{
  if * {
    ok := false;
  } else {
    ok := true;
  }
}

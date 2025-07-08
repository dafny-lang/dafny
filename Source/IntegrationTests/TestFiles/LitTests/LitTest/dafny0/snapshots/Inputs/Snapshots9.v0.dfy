method M() returns (ok: bool)
  ensures ok  // related location here
{
  if * {  // error: postcondition failure on this return path
    ok := false;
  } else {
    ok := true;
  }
}

method P() returns (ok: bool)
  ensures ok  // related location here
{  // error: postcondition failure on this return path
}

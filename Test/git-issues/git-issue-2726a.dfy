// RUN: %dafny /compile:3 /compileTarget:cs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const digits := ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"]

function IntToString(i: int): string   
  decreases i < 0, if i<0 then -i else i
{
  if i < 0 then ("-" + IntToString(-i))
  else if i < 10 then digits[i]  
  else if i < 100 then (digits[i/10] + digits[i%10])
  //else ("DDD" + digits[i%10])
  else (IntToString(i/10) + digits[i%10])  // CRASHES
}

method Main() {
  print IntToString(4), "\n";
  print IntToString(42), "\n";
  print IntToString(422), "\n";
}

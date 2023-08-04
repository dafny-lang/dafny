// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function SpecConverter(input: string): int {
  1
}

type StringWrapper {
  ghost const base: string
}

method Converter(value: StringWrapper) returns (res: int)
  // the following postcondition used to not verify
  ensures res == SpecConverter(value.base)
{
  res := 1;
}

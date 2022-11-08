// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "./AbstractFileIO.dfy"

abstract module AbstractTest {
  import FileIO : AbstractFileIO

  function method ExpectedErrorMessagePrefix(): string

  method Main(args: seq<string>) {
    {
      var str := "Hello world\nGoodbye\n";
      var bytes := seq(|str|, i requires 0 <= i < |str| => str[i] as bv8);

      expect |args| == 2;
      var dataFilePath := args[1];

      var res := FileIO.WriteBytesToFile(dataFilePath, bytes);
      expect res.Success?, "unexpected failure: " + res.error;
    }

    {
      var res := FileIO.WriteBytesToFile("", []);
      expect res.Failure?, "unexpected success";
      expect ExpectedErrorMessagePrefix() <= res.error, "unexpected error message: " + res.error;
    }
  }
}

// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "./AbstractFileIO.dfy"

abstract module AbstractTest {
  import AbstractFileIO : AbstractFileIO

  function method ExpectedErrorMessagePrefix(): string

  method Main(args: seq<string>) {
    {
      // Ideally we would define `str` as a constant and compute `bytes` automatically.
      // To do so, we would need to convert each `char` in `str` to a `bv8` value, by using `as bv8`.
      // But that triggers a bug in the Java compiler: <https://github.com/dafny-lang/dafny/issues/2942>.
      // So for now we settle for manually writing out the desired `bytes`,
      // and statically verifying that these values match the characters of `str`.
      ghost var str := "Hello world\nGoodbye\n";
      var bytes: seq<bv8> := [
        // "Hello world\n"
        0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x0a,
        // "Goodbye\n"
        0x47, 0x6f, 0x6f, 0x64, 0x62, 0x79, 0x65, 0x0a
      ];
      assert forall i | 0 <= i < |bytes| :: bytes[i] as int == str[i] as int;

      expect |args| == 2;
      var dataFilePath := args[1];

      var res := AbstractFileIO.WriteBytesToFile(dataFilePath, bytes);
      expect res.Success?, "unexpected failure: " + res.error;
    }

    {
      var res := AbstractFileIO.WriteBytesToFile("", []);
      expect res.Failure?, "unexpected success";
      expect ExpectedErrorMessagePrefix() <= res.error, "unexpected error message: " + res.error;
    }
  }
}

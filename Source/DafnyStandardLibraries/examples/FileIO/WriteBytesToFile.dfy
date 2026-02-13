/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module WriteBytesToFile {
  import Std.FileIO

  @Test
  method Test() {
    // TODO: extern function for the expected error prefix
    theMain("build/../build/fileioexamples", "");
  }

  @ResourceLimit("2e6")
  method theMain(outputDir: string, expectedErrorPrefix: string) {

      // Happy paths: write files to the output dir. (The %diff LIT commands check that we wrote the correct content.)
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

        // Write directly into the output directory
      {
        var res := FileIO.WriteBytesToFile(outputDir + "/output_plain", bytes);
        expect res.Success?, "unexpected failure writing to output_plain: " + res.error;
      }
        // Ensure that nonexistent parent directories are created as necessary
      {
        var res := FileIO.WriteBytesToFile(outputDir + "/foo/bar/output_nested", bytes);
        expect res.Success?, "unexpected failure writing to output_nested: " + res.error;
      }
        // Ensure that file paths with .. are handled correctly
      {
        var res := FileIO.WriteBytesToFile(outputDir + "/foo/bar/../output_up", bytes);
        expect res.Success?, "unexpected failure writing to output_up: " + res.error;
      }
    }

      // Failure path: attempting to write to a blank file path should never work.
    {
      var res := FileIO.WriteBytesToFile("", []);
      expect res.Failure?, "unexpected success";
      expect expectedErrorPrefix <= res.error, "unexpected error message: " + res.error;
    }
  }
}

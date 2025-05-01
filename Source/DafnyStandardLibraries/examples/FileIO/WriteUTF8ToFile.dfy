/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module WriteToFile {
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
      var str := "Hello world\nGoodbye\n";

        // Write directly into the output directory
      {
        var res := FileIO.WriteUTF8ToFile(outputDir + "/output_plain", str);
        expect res.Pass?, "unexpected failure writing to output_plain: " + res.error;
        var readAgain := FileIO.ReadUTF8FromFile(outputDir + "/output_plain");
        expect readAgain.Success?;
        expect readAgain.value == str;
      }
        // Ensure that nonexistent parent directories are created as necessary
      {
        var res := FileIO.WriteUTF8ToFile(outputDir + "/foo/bar/output_nested", str);
        expect res.Pass?, "unexpected failure writing to output_nested: " + res.error;
      }
        // Ensure that file paths with .. are handled correctly
      {
        var res := FileIO.WriteUTF8ToFile(outputDir + "/foo/bar/../output_up", str);
        expect res.Pass?, "unexpected failure writing to output_up: " + res.error;
      }
    }

      // Failure path: attempting to write to a blank file path should never work.
    {
      var res := FileIO.WriteUTF8ToFile("", []);
      expect res.Fail?, "unexpected success";
      expect expectedErrorPrefix <= res.error, "unexpected error message: " + res.error;
    }
  }
}

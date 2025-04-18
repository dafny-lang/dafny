/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module ReadFromFile {
  import Std.FileIO

  @Test
  method Test() {
    // TODO: extern function for the expected error prefix
    theMain("examples/FileIO/../FileIO/data.txt", "");
  }

  method theMain(dataPath: string, expectedErrorPrefix: string) {

      // Happy path: read from the data file, and check that we see the expected content.
    {
      var expectedStr := "Hello world\nGoodbye\n";
      var res := FileIO.ReadFile(dataPath);
      expect res.Success?, "unexpected failure: " + res.error;
      expect res.value == expectedStr;
    }

      // Failure path: attempting to read from a blank file path should never work.
    {
      var res := FileIO.ReadFile("");
      expect res.Failure?, "unexpected success";
      expect expectedErrorPrefix <= res.error, "unexpected error message: " + res.error;
    }
  }
}

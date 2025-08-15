/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// A Dafny program that reads itself - demonstrating FileIO with Rust backend
module SelfReader {
  import opened Std.Wrappers
  import Std.FileIO

  method {:main} Main() {
    // Read this very file
    var filename := "Source/DafnyStandardLibraries/examples/SelfReader.dfy";
    
    var readResult := FileIO.ReadBytesFromFile(filename);
    match readResult {
      case Success(content) => {
        print "Successfully read ", |content|, " bytes from ", filename, "\n";
        
        // Convert bytes to string and show first few lines
        var contentStr := seq(|content|, i requires 0 <= i < |content| => content[i] as char);
        var lines := SplitLines(contentStr);
        
        print "First few lines of this file:\n";
        var linesToShow := if |lines| < 10 then |lines| else 10;
        for i := 0 to linesToShow {
          print "  ", lines[i], "\n";
        }
        
        print "This program successfully read itself using Rust FileIO!\n";
      }
      case Failure(error) => {
        print "Failed to read file: ", error, "\n";
      }
    }
  }
  
  // Helper method to split content into lines
  method SplitLines(content: string) returns (lines: seq<string>) {
    lines := [];
    var currentLine := "";
    
    for i := 0 to |content| {
      if content[i] == '\n' {
        lines := lines + [currentLine];
        currentLine := "";
      } else {
        currentLine := currentLine + [content[i]];
      }
    }
    
    // Add the last line if it doesn't end with newline
    if |currentLine| > 0 {
      lines := lines + [currentLine];
    }
  }
}

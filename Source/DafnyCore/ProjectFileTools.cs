// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.IO;
using Tomlyn;
using Tomlyn.Model;
using Tomlyn.Syntax;
using Bpl = Microsoft.Boogie;

//Called to read project file options everytime
// - that means we can't let users pass options which don't have values using project file.

// Called when a /project is passed and that runs Dafny for all files.
//  - find where file name is used.


namespace Microsoft.Dafny {
  
  public class ProjectFileTools {
    
    
    public static string[] ProjectParser() {
      string projectFile = String.Empty;
      try {
        projectFile = File.ReadAllText("dafny.toml");
      }
      catch {
        return null;
      }
      var model = Toml.Parse(projectFile).ToModel();
      string[] projectArgs = Array.Empty<string>();
      try {
        var commandTable = (TomlTable) (model["Command"]);
        foreach (KeyValuePair<string, object> entry in (commandTable)) {
          projectArgs = projectArgs.Append("" + entry.Value).ToArray();
        }
        var ArgTable = (TomlTable) (model["Arguments"]);
        foreach (KeyValuePair<string, object> entry in (ArgTable)) {
          projectArgs = projectArgs.Append("--" + entry.Key + ":" + entry.Value).ToArray();
        }
      } catch {
        projectArgs = null;
      }
      return projectArgs;
    }

    public static String[] DafnyFileList() {
      string path = Directory.GetCurrentDirectory();
      string filter = "*.dfy";
      string[] directoryEntries = Directory.GetFileSystemEntries(path, filter,SearchOption.AllDirectories);
      return directoryEntries;
    }

    /*public static void ProjectRun(String[] ListofFiles, string[] ProjectArguments) {
    }*/
    
  }
}
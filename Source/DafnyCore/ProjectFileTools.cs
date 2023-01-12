// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;
using Microsoft.VisualBasic.CompilerServices;
using Tomlyn;
using Tomlyn.Helpers;
using Tomlyn.Model;
using Tomlyn.Parsing;
using Tomlyn.Syntax;
using Bpl = Microsoft.Boogie;

//Called to read project file options everytime
// - that means we can't let users pass options which don't have values using project file.

// Called when a /project is passed and that runs Dafny for all files.
//  - find where file name is used.


namespace Microsoft.Dafny {
  
  public class ProjectFileTools {
    
    
    public static string[] ProjectParser() {
      var ProjectOptions = new DafnyOptions();
      var optionValues = new Dictionary<Option, object>();
      string projectFile = File.ReadAllText("/Users/prvshah/Documents/prv-dafny/dafny/Test/comp/firstSteps/dafny.toml");
      if (projectFile == null) {
          throw new Exception();
        }
      DocumentSyntax syntax = Toml.Parse(projectFile);
      var model = syntax.ToModel(); 
      var toml = (TomlTable) (model["Options"]);
      string[] projectArgs = {};
      foreach (KeyValuePair<string, object> entry in (toml)) {

          projectArgs = projectArgs.Append( "/" + entry.Key + ":" + entry.Value).ToArray();
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
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using Microsoft.Extensions.FileSystemGlobbing;
using Microsoft.Extensions.FileSystemGlobbing.Abstractions;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions {
  public class FileDataAttribute : DataAttribute {
    public string? Directory { get; set; }
    public string[]? Includes { get; set; }
    public string[]? Excludes { get; set; }

    public override IEnumerable<object[]> GetData(MethodInfo testMethod) {
      var matcher = new Matcher();

      if (Includes != null) {
        foreach (var include in Includes) {
          matcher.AddInclude(include);
        }
      }

      if (Excludes != null) {
        foreach (var exclude in Excludes) {
          matcher.AddExclude(exclude);
        }
      }

      var basePath = Directory ?? Path.Combine("TestFiles", testMethod.DeclaringType!.Name, testMethod.Name);
      var result = matcher.Execute(new DirectoryInfoWrapper(new DirectoryInfo(basePath)));
      if (!result.HasMatches) {
        throw new ArgumentException("No matching files found: " + this);
      }

      return result.Files.Select(file => {
        var fullPath = Path.Join(basePath, file.Stem);
        var row = new FileTheoryDataRow(fullPath) {
          SourceInformation = new SourceInformation() { FileName = fullPath, LineNumber = 0 },
          TestDisplayName = file.Stem,
        };
        return new[] { row };
      });
    }
  }
}
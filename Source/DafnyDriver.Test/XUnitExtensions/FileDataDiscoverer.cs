using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace DafnyDriver.Test.XUnitExtensions {
  public abstract class FileDataDiscoverer : IDataDiscoverer {
    protected string GetBasePath(IAttributeInfo attributeInfo, IMethodInfo testMethod) {
      var path = attributeInfo.GetNamedArgument<string>(nameof(FileDataAttribute.Path));

      if (path != null) {
        return path;
      }

      return Path.Combine("TestFiles", testMethod.ToRuntimeMethod().DeclaringType.Name, testMethod.Name);
    }

    public IEnumerable<object[]> GetData(IAttributeInfo attributeInfo, IMethodInfo testMethod) {
      var path = GetBasePath(attributeInfo, testMethod);
      var extension = attributeInfo.GetNamedArgument<string>(nameof(FileDataAttribute.Extension));

      if (Directory.Exists(path)) {
        return Directory.EnumerateFiles(path, "*" + extension, SearchOption.AllDirectories)
          .SelectMany(childPath => FileData(attributeInfo, testMethod, childPath));
      }

      var fileName = path + extension;
      if (File.Exists(fileName)) {
        return FileData(attributeInfo, testMethod, fileName);
      }

      throw new ArgumentException("No data found for path: " + path);
    }

    public abstract bool SupportsDiscoveryEnumeration(IAttributeInfo dataAttribute, IMethodInfo testMethod);

    protected abstract IEnumerable<object[]> FileData(IAttributeInfo attributeInfo, IMethodInfo testMethod, string fileName);
  }
}
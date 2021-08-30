using System.Collections.Generic;
using System.Reflection;
using Xunit.Sdk;

namespace DafnyDriver.Test.XUnitExtensions {
  public abstract class FileDataAttribute : DataAttribute {
    public readonly string Path;
    public readonly string Extension;

    public FileDataAttribute(string path = null, string extension = null) {
      Path = path;
      Extension = extension;
    }

    public override IEnumerable<object[]> GetData(MethodInfo testMethod) {
      throw new System.NotImplementedException();
    }
  }
}
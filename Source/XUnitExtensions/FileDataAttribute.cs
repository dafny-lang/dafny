using System.Collections.Generic;
using System.Reflection;
using Xunit.Sdk;

namespace XUnitExtensions {
  public abstract class FileDataAttribute : DataAttribute {
    public virtual string Path { get; set; }

    public virtual string Extension { get; set; }

    public override IEnumerable<object[]> GetData(MethodInfo testMethod) {
      throw new System.NotImplementedException();
    }
  }
}
using System.Collections.Generic;
using Xunit.Abstractions;

namespace XUnitExtensions {
  public class FileTheoryDataRow : IXunitSerializable, IFileTheoryRowData {

    private object[]? data;

    public FileTheoryDataRow() {

    }

    public FileTheoryDataRow(params object[] data) {
      this.data = data;
    }

    public ISourceInformation? SourceInformation { get; set; }
    public string? Skip { get; set; }
    public string? TestDisplayName { get; set; }
    public Dictionary<string, List<string>>? Traits { get; set; }
    public object?[] GetData() => data!;

    public void Serialize(IXunitSerializationInfo info) {
      info.AddValue(nameof(SourceInformation), SourceInformation);
      info.AddValue(nameof(Skip), Skip);
      info.AddValue(nameof(TestDisplayName), TestDisplayName);
      info.AddValue(nameof(Traits), Traits);
      info.AddValue(nameof(data), data);
    }

    public void Deserialize(IXunitSerializationInfo info) {
      SourceInformation = info.GetValue<ISourceInformation>(nameof(SourceInformation));
      Skip = info.GetValue<string>(nameof(Skip));
      TestDisplayName = info.GetValue<string>(nameof(TestDisplayName));
      Traits = info.GetValue<Dictionary<string, List<string>>>(nameof(Traits));
      data = info.GetValue<object[]>(nameof(data));
    }
  }
}
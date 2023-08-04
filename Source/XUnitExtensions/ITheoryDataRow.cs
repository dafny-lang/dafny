using System.Collections.Generic;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;

namespace XUnitExtensions {
  public interface IFileTheoryRowData {

    /// <summary>
    /// Gets the source information for this row of data; if <c>null</c> is returned, then the location
    /// of the test method is ussed.
    /// </summary>
    ISourceInformation? SourceInformation { get; }

    /// <summary>
    /// Gets the reason for skipping this row of data; if <c>null</c> is returned, then the data
    /// row isn't skipped.
    /// </summary>
    string? Skip { get; }

    /// <summary>
    /// Gets the display name for the test (replacing the default behavior, which would be to use the DisplayName
    /// from <see cref="FactAttribute"/>, or falling back to the class &amp; method name).
    /// </summary>
    string? TestDisplayName { get; }

    /// <summary>
    /// Gets the trait values associated with this theory data row. If there are none, you may either
    /// return a <c>null</c> or empty dictionary.
    /// </summary>
    Dictionary<string, List<string>>? Traits { get; }

    /// <summary>
    /// Gets the theory data.
    /// </summary>
    object?[] GetData();
  }
}
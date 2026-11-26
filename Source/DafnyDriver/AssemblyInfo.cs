using System.Runtime.CompilerServices;

// MeasureComplexityCommand is internal, so its resource-count accumulator is otherwise unreachable
// from a test. This project sets GenerateAssemblyInfo=false, so the attribute has to be written out
// rather than declared as an MSBuild InternalsVisibleTo item, which would be silently ignored.
[assembly: InternalsVisibleTo("DafnyDriver.Test")]

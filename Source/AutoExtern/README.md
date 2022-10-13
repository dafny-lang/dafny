# Automatically generating Dafny traits from C# code

This project implements a (limited, Dafny-internal) tool that generates Dafny
traits from C# class hierarchies.

Only interfaces, classes, fields, and properties are exported: functions and
methods are not reflected in the generated traits.  Hence, this feature is
mostly useful for data classes.  Internally, we use it to expose `DafnyAst.cs`
to Dafny.

`AutoExtern` is an internal tool and is not part of the standard Dafny release,
but you can follow [the tutorial](../AutoExtern.Test/Tutorial/README.md) if you
want to see what it can do.

## Usage

```
dotnet run <Project.csproj> <RootNamespace> <Template.dfy> \
    <CSharpModel.dfy> <Output.dfy> <SourceFile.cs> [<SourceFile.cs> ...]
```

The tool takes six arguments:

- The name of a C# project.  This is used to compile `SourceFile.cs` and gather
  semantic information about it using Roslyn (the C# compiler).  We need this to
  disambiguate type names.

- A root namespace — names in that namespace will not be fully qualified.

- A template file in which to insert the generated definitions.  There are
  likely project-specific types in `SourceFile.cs` that you want to model by
  hand, and your template file should `include` these models.  This template
  must contain the string `{{{AutoExtern}}}`.

- A path where `AutoExtern` should save `CSharpModel.dfy`, or `""` to skip
  writing the model.

- A path to write the generated model to.

- The name of one or more source files to translate to Dafny.  Only interfaces
  and classes are supported, and within those only fields and properties are
  exported.

Additionally, the tool supports an optional `--rewrite` flag, which may be
repeated. `--rewrite A:B` indicates that the prefix `A` should be rewritten to
`B` when translating names. This is useful when the template imports other
modules, or when a model combines manually and automatically translated elements
(see [the tutorial](../AutoExtern.Test/Tutorial/README.md) for an example).

## Example

This example is from [`../AutoExtern.Test/Minimal`](../AutoExtern.Test/Minimal/)

Take this C# code and the following template:

```csharp
namespace NS;

public interface Intf {
  public string Prop { get; }
}

public class Impl : Intf {
  public int Field;
  public string Prop => Field.ToString();
}
```

```dafny
include "CSharpModel.dfy"

module {:compile false} {:extern "NS"} NSModel {
  import System

{{{AutoExtern}}}
}
```

Here is what `AutoExtern` generates:

```
$ dotnet run Library.csproj NS Library.dfy.template CSharpModel.dfy Library.dfy Library.cs
```

```dafny
include "CSharpModel.dfy"

module {:compile false} {:extern "NS"} NSModel {
  import System

  trait {:compile false} {:extern} Intf {
    var {:extern "Prop"} Intf_Prop: System.String // interface property
  }

  trait {:compile false} {:extern} Impl extends Intf {
    var Field: System.int32
    var Prop: System.String // property
  }

}
```

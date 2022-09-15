# DafnyLS

*DafnyLS* is a [language server](https://microsoft.github.io/language-server-protocol/) for [Dafny](https://github.com/dafny-lang/dafny). It is implemented in C# on .NET with OmniSharp's [C# Language Server Protocol](https://github.com/OmniSharp/csharp-language-server-protocol).


## Running

Place the [Z3 executable](https://github.com/Z3Prover/z3/releases/tag/Z3-4.8.5) in the language server's root directory or within the `z3/bin` subdirectory (already present in the [release](https://github.com/dafny-lang/dafny/releases) packages). If not on windows, ensure that the executable has execution permissions:

```sh
chmod u+x ./z3/bin/z3
```

The language server can be started either by the executable itself (e.g., `DafnyLanguageServer.exe` on windows) or with the following command.

```sh
dotnet DafnyLanguageServer.dll
```

## Configuration

The language server can be configured using the `DafnyLanguageServer.appsettings.json` file as well as using CLI arguments.

For example, if you want to configure the automatic verification through the command line:

```sh
dotnet DafnyLanguageServer.dll --documents:verify=onsave
```

Or using the `DafnyLanguageServer.appsettings.json` configuration file:

```json
{
  "Documents": {
    "Verify": "onsave"
  }
}
```

Options provided through the command line have higher priority than the options provided within `DafnyLanguageServer.appsettings.json`.


### Documents

```sh
# Sets when the automatic verification should be applied.
# Options:
# - never - Never verifies the document.
# - onchange - Verifies the document with each change.
# - onsave - Verifies the document each time it is saved.
# default: onchange
--documents:verify=onchange
```

### Verifier

```sh
# Sets maximum execution time (in seconds) for verifications
# Default: 0 (no time limit)
--verifier:timelimit=0

# Sets the maximum number of virtual cores to use. 
# Default: 0 (use half of the available virtual cores).
--verifier:vcscores=0

# Set the caching policy (like /verifySnapshots for Dafny.exe)
# Default: 0 (no caching).
--verifier:verifysnapshots=0

# Set whether or not to compute and report verification gutter statuses
# Default: 0 (no gutter status reported).
--verifier:gutterStatus=true
```

### Ghost Diagnostics

```sh
# Mark ghost statements
# Default: true (mark the statements)
--ghost:markStatements=true
```

### Plugins

```sh
# Provides a path to assemblies and optional space-separated command-line arguments after a comma.
# Repeat with --dafny:plugins:0=... --dafny:plugins:1=... for multiple plugins.
--dafny:plugins:0=path\to\example.dll
--dafny:plugins:0=path/to/example2.dll,oneArgument
--dafny:plugins:0=example3.dll,"firstArgument with \" space and quote" secondArgument

# On the command-line, you'd use the following escapes for the first and third examples:
"--dafny:plugins:0=path\\to\\example.dll"
"--dafny:plugins:0=example3.dll,\"firstArgument with \\\" space and quote\" secondArgument"

# For just the dafny executable, replace `--dafny:plugins:X` by `--plugin:` that you can repeat.
```

#### About plugins

*Plugins are experimental.
The plugin API directly exposes the Dafny AST, which is constantly evolving.
Hence, always recompile your plugin against the binary of Dafny that will be importing your plugin.*

Plugins are libraries linked to a `Dafny.dll` of the same version than the language server.
A plugin typically defines:

* Zero or one class extending `Microsoft.Dafny.Plugins.PluginConfiguration` which receives plugins arguments in their method `ParseArguments`, and
  1) Can return a list of `Microsoft.Dafny.Plugins.Rewriter`s when their method `GetRewriters()` is called by Dafny,
  2) Can return a list of `Microsoft.Dafny.Plugins.Compiler`s when their method `GetCompilers()` is called by Dafny,
  3) If the configuration extends the subclass `Microsoft.Dafny.LanguageServer.Plugins.PluginConfiguration`,
     then it can return a list of `Microsoft.Dafny.LanguageServer.Plugins.DafnyCodeActionProvider`s when their method `GetDafnyCodeActionProviders()` is called by the Dafny Language Server.

* Zero or more classes extending `Microsoft.Dafny.Plugins.Rewriter`.
  If a configuration class is provided, it is responsible for instantiating them and returning them in `GetRewriters()`.
  If no configuration class is provided, an automatic configuration will load every defined `Rewriter` automatically.
* Zero or more classes extending `Microsoft.Dafny.Plugins.Compiler`.
  If a configuration class is provided, it is responsible for instantiating them and returning them in `GetCompilers()`.
  If no configuration class is provided, an automatic configuration will load every defined `Compiler` automatically.
* Zero or more classes extending `Microsoft.Dafny.LanguageServer.Plugins.DafnyCodeActionProvider`.
  Only a configuration class of type `Microsoft.Dafny.LanguageServer.Plugins.PluginConfiguration` can be responsible for instantiating them and returning them in `GetDafnyCodeActionProviders()`.

The most important methods of the class `Rewriter` that plugins override are
* (experimental) `PreResolve(ModuleDefinition)`: Here you can optionally modify the AST before it is resolved.
* `PostResolve(ModuleDefinition)`: This method is repeatedly called with every resolved and type-checked module, before verification.
  Plugins override this method typically to report additional diagnostics.
* `PostResolve(Program)`: This method is called once after all `PostResolve(ModuleDefinition)` have been called.

Plugins are typically used to report additional diagnostics such as unsupported constructs for specific compilers (through the methods `Èrror(...)` and `Warning(...)` of the field `Reporter` of the class `Rewriter`)

Note that all plugin errors should use the original program's expressions' token and NOT `Token.NoToken`, else no error will be displayed in the IDE.

## Code actions plugin tutorial

In this section, we will create a plugin to provide more code actions to Dafny.
The code actions will be simple: Add a dummy comment in front of the first method name,
if the selection is on the line of the method.

Assuming the Dafny source code is installed in the folder `dafny/`
start by creating an empty folder next to it, e.g. `PluginTutorial/`

```
> mkdir PluginTutorial
> cd PluginTutorial
```
Then, create a dotnet class project
```
> dotnet new classlib
```
It will create a file `Class1.cs` that you can rename
```
> mv Class1.cs PluginAddComment.cs
```
Open the newly created file `PluginTutorial.csproj`, and add the following after `</PropertyGroup>`:
```
  <ItemGroup>
    <ProjectReference Include="../dafny/source/DafnyLanguageServer/DafnyLanguageServer.csproj" />
  </ItemGroup>
```


Then, open the file `PluginAddComment.cs`, remove everything, and write the imports and a namespace:

```csharp
using Microsoft.Dafny;
using Microsoft.Dafny.LanguageServer.Plugins;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using System.Linq;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace PluginAddComment;
```

After that, add a `PluginConfiguration` that will expose all the quickfixers of your plugin.
This class will be discovered and instantiated automatically by Dafny.
```
public class TestConfiguration : PluginConfiguration {
  public override DafnyCodeActionProvider[] GetDafnyCodeActionProviders() {
    return new DafnyCodeActionProvider[] { new AddCommentDafnyCodeActionProvider() };
  }
}
```
Note that you could also override the methods `GetRewriters()` and `GetCompilers()` for other purposes, but this is out of scope for this tutorial.

Then, we need to create the quickFixer `AddCommentDafnyCodeActionProvider` itself:

```
public class AddCommentDafnyCodeActionProvider : DafnyCodeActionProvider {
  public override IEnumerable<DafnyCodeAction> GetDafnyCodeActions(IDafnyCodeActionInput input, Range selection) {
    return new DafnyCodeAction[] { };
  }
}
```

For now, this quick fixer returns nothing. `input` is the program state, and `selection` is where the caret is.
We replace the return statement with a conditional that tests whether the selection is on the first line:
```
    var firstTokenRange = input.Program?.GetFirstTopLevelToken()?.GetLspRange();
    if(firstTokenRange != null && firstTokenRange.Start.Line == selection.Start.Line) {
      return new DafnyCodeAction[] {
        // TODO
      };
    } else {
      return new DafnyCodeAction[] { };
    }
```

Every quick fix consists of a title (provided immediately), and zero or more `DafnyCodeActionEdit` (computed lazily).
An `DafnyCodeActionEdit` has a `Range` to remove and some `string` to insert instead. All `DafnyCodeActionEdit`
of the same `DafnyCodeAction` are applied at the same time if selected.

To create a `DafnyCodeAction`, we can either use the easy-to-use `InstantDafnyCodeAction`, which accepts a title and an array of edits:
```
  return new DafnyCodeAction[] {
    new InstantDafnyCodeAction("Insert comment", new DafnyCodeActionEdit[] {
      new DafnyCodeActionEdit(firstTokenRange.GetStartRange(), "/*First comment*/")
    })
  };
```

or we can implement our custom inherited class of `DafnyCodeAction`:
```
public class CustomDafnyCodeAction: DafnyCodeAction {
  public Range whereToInsert;
  
  public CustomDafnyCodeAction(Range whereToInsert): base("Insert comment") {
    this.whereToInsert = whereToInsert;
  }
  public override DafnyCodeActionEdit[] GetEdits() {
    return new DafnyCodeActionEdit[] {
      new DafnyCodeActionEdit(whereToInsert.GetStartRange(), "/*A comment*/")
    };
  }
}
```
In that case, we could return:
```
  return new DafnyCodeAction[] {
    new CustomDafnyCodeAction(firstTokenRange)
  };
```

That's it! Now, build your library while inside your folder:
```
> dotnet build
```

This will create the file `PluginTutorial/bin/Debug/net6.0/PluginTutorial.dll`.
Now, open VSCode, open Dafny settings, and enter the absolute path to this DLL in the plugins section.
Restart VSCode, and it should work!
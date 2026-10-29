// NONUNIFORM: tests the implicit lib target used for dependency projects
// A dependency project is built through DafnyNewCli.HandleDafnyProject, which constructs a
// LibraryBackend itself rather than taking -t=lib from the command line. That is a second
// entry into the guard fixed for https://github.com/dafny-lang/dafny/issues/6485, so it
// needs its own test: StandardLibraries_LibBuild.dfy only covers the explicit -t=lib path.
// RUN: %verify --standard-libraries:true "%s" --library "%S/Inputs/fileIOProject/dfyconfig.toml" > "%t"
// RUN: %diff "%s.expect" "%t"
module DepMain {
  import UsesFileIO

  method Uses(p: string)
    decreases *
  {
    UsesFileIO.WriteGreeting(p);
  }
}

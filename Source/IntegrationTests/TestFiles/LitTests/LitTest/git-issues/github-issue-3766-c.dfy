// RUN: %testDafnyForEachCompiler "%s"

// Running this using the Java backend used to cause an NPE
// because Tree's default value would be initialized using Tree's
// type descriptor (since it has no non-recursive constructors)
// before it was initialized
datatype Tree = Tree(ts : seq<Tree>)

method Main() {
  var tree: Tree := Tree([]);
}
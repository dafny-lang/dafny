// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var children: seq<Node>
}

datatype Path<T> = Empty | Extend(Path, T)

predicate Reachable(source: Node, sink: Node, S: set<Node>)
  reads S
{
  exists via: Path<Node> :: ReachableVia(source, via, sink, S)
}

predicate {:older p} ReachableVia(source: Node, p: Path<Node>, sink: Node, S: set<Node>)

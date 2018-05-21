function DisproofLemma(p: seq<Node>, subgraph: set<Node>,
            root: Node, goal: Node, graph: set<Node>): bool
   requires closed(subgraph) && closed(graph) && subgraph <= graph;
   requires root in subgraph && goal !in subgraph && goal in graph;
   reads p;
   ensures DisproofLemma(p, subgraph, root, goal, graph);
   ensures !pathSpecific(p, root, goal, graph);
{
   1 < |p| && p[0] == root && p[|p|-1] == goal ==>
      (p[1] in p[0].next ==> DisproofLemma(p[1..], subgraph, p[1], goal, graph))
}

ghost method ClosedLemma(subgraph: set<Node>, root: Node, goal: Node, graph: set<Node>)
   requires closed(subgraph) && closed(graph) && subgraph <= graph;
   requires root in subgraph && goal !in subgraph && goal in graph;
   ensures !(exists p: seq<Node> :: pathSpecific(p, root, goal, graph));
{
   assert forall p :: DisproofLemma(p, subgraph, root, goal, graph);
}

class Node
{
   var next: seq<Node>;
}

function pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>): bool
   reads p;
   requires closed(graph);
{
   0 < |p| && // path is non-empty
   start == p[0] && end == p[|p|-1] && // it starts and ends correctly
   path(p, graph) // and it is a valid path
}

function path(p: seq<Node>, graph: set<Node>): bool
   requires closed(graph) && 0 < |p|;
   reads p;
   decreases |p|;
{
   p[0] in graph &&
   (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
      path(p[1..], graph)) // and the rest of the sequence is a valid
}

function closed(graph: set<Node>): bool
   reads graph;
{
   null !in graph && // graphs can only consist of actual nodes, not null.
   forall i :: i in graph ==> (forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i)
}
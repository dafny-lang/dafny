// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// map types used to slip through type checking of reads/modifies clauses

class MyClass { }

function fset(M: set<MyClass>): real
  reads M
function fiset(M: iset<MyClass>): real
  reads M

function fmultiset(M: multiset<MyClass>): real
  reads M

function fseq(M: seq<MyClass>): real
  reads M

function fmap(M: map<MyClass,MyClass>): real
  reads M  // error: cannot use map here
function fimap(M: imap<MyClass,MyClass>): real
  reads M  // error: cannot use imap here
function fmapKeys(M: map<MyClass,MyClass>): real
  reads M.Keys
function fimapKeys(M: imap<MyClass,MyClass>): real
  reads M.Keys
function fmapValues(M: map<MyClass,MyClass>): real
  reads M.Values
function fimapValues(M: imap<MyClass,MyClass>): real
  reads M.Values

method mset(M: set<MyClass>)
  modifies M
method miset(M: iset<MyClass>)
  modifies M

method mmultiset(M: multiset<MyClass>)
  modifies M

method mseq(M: seq<MyClass>)
  modifies M

method mmap(M: map<MyClass,MyClass>)
  modifies M  // error: cannot use map here
method mimap(M: imap<MyClass,MyClass>)
  modifies M  // error: cannot use imap here
method mmapKeys(M: map<MyClass,MyClass>)
  modifies M.Keys
method mimapKeys(M: imap<MyClass,MyClass>)
  modifies M.Keys
method mmapValues(M: map<MyClass,MyClass>)
  modifies M.Values
method mimapValues(M: imap<MyClass,MyClass>)
  modifies M.Values

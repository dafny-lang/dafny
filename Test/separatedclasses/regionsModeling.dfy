// Region soundness modeling in Dafny
// - One struct with one ghost field Region: object? and a value x: int
// - One heap as an array of structs.
// - References are indices
// - Methods can take one or two arguments which are objects or ints
// - Methods have reads and modifies clauses
// - Statements are not nested and either
//     - Skip(n) where n is a number of statements
//     - assert object.field == value;
//     - assign dereference field to local variaHeapUpdateble
//     - assign value to local variable
//     - assign local variable to deference field
//     - conditional branching with object.field == value
//     - call method on local reference
// - We check if objects being read and modified are in the correct clauses
// - We can create references
// - Threads have each their own stack.
// Verification should be like type-checking.
// We need a deterministic evaluator, and prove our evaluator will never get stuck.
// Property: If a code was verified, meaning all its assertions can be assumed, then its is never stuck



module Random {
  export provides RNG, randomBool
  type RNG = nat -> bool
  function next(rng: RNG): RNG {
    (i: nat) => rng(i + 1)
  }
  function randomBool(rng: RNG): (bool, RNG) {
    (rng(0), next(rng))
  }
}

import opened Random

type Heap = seq<StructVal>

function HeapUpdate(heap: Heap, reference: nat, field: Field, v: Value): Heap
  requires reference < |heap|
{
  heap[reference := heap[reference].assign(field, v)]
}

datatype Field = ValueField | RegionField | ReferenceField
{
  predicate IsGhost() { !RegionField? }
  predicate IsObject() { !ValueField? }
  function getType(): Type { if ValueField? then Value else Reference }
}

datatype LocalVar = A | B | C

datatype MethodRef = MA | MB | MC | MD

datatype Option<T> = None | Some(value: T)

datatype TypeMap = TypeMap(aType: Type, bType: Type, cType: Type)
{
  function update(name: LocalVar, newType: Type): TypeMap {
    match name {
      case A => this.(aType := newType)
      case B => this.(bType := newType)
      case C => this.(cType := newType)
    }
  }
  lemma updateTypeTest() {
    assert TypeMap(Value,     Reference, Reference).update(A, Reference)
        == TypeMap(Reference, Reference, Reference);
    assert TypeMap(Reference, Value,     Reference).update(B, Reference)
        == TypeMap(Reference, Reference, Reference);
    assert TypeMap(Reference, Reference, Value    ).update(C, Reference)
        == TypeMap(Reference, Reference, Reference);
  }
  function get(name: LocalVar): Type {
    match name {
      case A => aType
      case B => bType
      case C => cType
    }
  }
  lemma getTypeTest() {
    assert TypeMap(Value,     Reference, Reference).get(A) == Value;
    assert TypeMap(Reference, Value,     Reference).get(B) == Value;
    assert TypeMap(Reference, Reference, Value    ).get(C) == Value;
  }
}

datatype Statement =
  | AssignConst(target: LocalVar, value: int, next: Statement)
  | AssignRef(target: LocalVar, field: Field, localVar: LocalVar, next: Statement)   // Requires target != null
  | AssignDeref(target: LocalVar, localVar: LocalVar, field: Field, next: Statement) // Requires localVar != null
  | IfEq(localVar: LocalVar, localVar2: LocalVar, thn: Statement, els: Statement)
  | AssertEq(target: LocalVar, value: int, next: Statement)
  | Return(name: LocalVar)
  | AssignMethodCall(target: LocalVar, methodRef: MethodRef, argA: LocalVar, argB: LocalVar, argC: LocalVar, next: Statement)
{
  function getType(typeMap: TypeMap, codeState: CodeState): Option<Type> {
    match this {
      case Return(name) => Some(typeMap.get(name))
      case AssignConst(target, value, next) =>
        next.getType(typeMap.update(target, Value), codeState)
      case AssignRef(target, field, localVar, next) =>
        if typeMap.get(target) != Reference then None
        else if field.getType() != typeMap.get(localVar) then None
        else next.getType(typeMap, codeState)
      case AssignDeref(target, localVar, field, next) =>
        if typeMap.get(localVar) != Reference then None else
        next.getType(typeMap.update(target, field.getType()), codeState)
      case IfEq(localVar, localVar2, thn, els) =>
        if typeMap.get(localVar) != typeMap.get(localVar2) then None
        else
          var thnType := thn.getType(typeMap, codeState);
          var elsType := els.getType(typeMap, codeState);
          if thnType != elsType then None else thnType
      case AssignMethodCall(target, methodRef, argA, argB, argC, next) =>
        var methodDef := codeState.get(methodRef);
        if typeMap.get(argA) != methodDef.aType then None else
        if typeMap.get(argB) != methodDef.bType then None else
        if typeMap.get(argC) != methodDef.cType then None else
        next.getType(typeMap.update(target, methodDef.returnType), codeState)
      case AssertEq(target, value, next) =>
        if typeMap.get(target) != Value then None else
        next.getType(typeMap, codeState)
    }
  }
}
datatype Type = Value | Reference

// All methods have three local vars that can be assigned at call time, and return one local variable
datatype Method = Method(
  aType: Type, bType: Type, cType: Type,
  body: Statement,
  returnType: Type)
{
  // Verified means type-checking for now. We will add assertions afterwards
  predicate Verified(codeState: CodeState) {
    body.getType(TypeMap(aType, bType, cType), codeState) == Some(returnType)
  }
}
datatype StructDef = StructDef(name: string)

datatype CodeState =
  CodeState(mA: Method, mB: Method, mC: Method, mD: Method)
{
  function get(m: MethodRef): Method {
    match m
    case MA => mA
    case MB => mB
    case MC => mC
    case MD => mD
  }
  predicate Verified() {
    mA.Verified(this) && mB.Verified(this) && mC.Verified(this) && mD.Verified(this)
  }
}

datatype ThreadResult = ThreadUnsound | ThreadResult(heap: Heap, state: MethodStack)

datatype Value = LocalValueInt(n :int) | LocalValueRef(reference: nat) {
  function getType(): Type { if LocalValueInt? then Value else Reference }
  predicate InHeap(heap: Heap) { if LocalValueRef? then reference < |heap| else true }
}

datatype LocalState = LocalState(statement: Statement, a: Value, b: Value, c: Value, returnType: Type) {
  // What it means for a thread to be in a local
  ghost predicate Verified(codeState: CodeState, heap: Heap) {
    var typeMap := TypeMap(a.getType(), b.getType(), c.getType());
    && a.InHeap(heap) && b.InHeap(heap) && c.InHeap(heap)
    && statement.getType(typeMap, codeState) == Some(returnType)
  }
  lemma VerifiedDoesNotChangeOnHeapUpdate(codeState: CodeState, heap: Heap, reference: nat, field: Field, value: Value)
    requires reference < |heap|
    requires Verified(codeState, heap)
    ensures Verified(codeState, HeapUpdate(heap, reference, field, value))
  {

  }

  function next(newStatement: Statement): LocalState {
    this.(statement := newStatement)
  }
  function assign(name: LocalVar, value: Value): LocalState {
    match name {
      case A => this.(a := value)
      case B => this.(b := value)
      case C => this.(c := value)
    }
  }
  function get(name: LocalVar): Value {
    match name {
      case A => this.a
      case B => this.b
      case C => this.c
    }
  }
}

datatype MethodStack = StackNil | StackCons(head: LocalState, tail: MethodStack)
{
  function newHead(head2: LocalState): MethodStack
    requires StackCons?
  {
    StackCons(head2, tail)
  }
  ghost predicate Verified(codeState: CodeState, heap: Heap) {
    if StackNil? then true
    else head.Verified(codeState, heap) && tail.Verified(codeState, heap)
  }
  
  lemma VerifiedDoesNotChangeOnHeapUpdate(codeState: CodeState, heap: Heap, reference: nat, field: Field, value: Value)
    requires reference < |heap|
    requires Verified(codeState, heap)
    ensures Verified(codeState, HeapUpdate(heap, reference, field, value))
  {

  }

  function Evaluate(codeState: CodeState, heap: Heap): ThreadResult {
    if StackNil? then ThreadResult(heap, this) else
    var localState := head;
    var statement := localState.statement;
    match statement {
      case AssignConst(target, value, next) =>
        var newMethodStack := this.newHead(localState.next(statement.next).assign(target, LocalValueInt(value)));
        ThreadResult(heap, newMethodStack)
      case AssignRef(target, field, localVar, next) =>
        var ref := localState.get(target);
        if !ref.LocalValueRef? || ref.reference >= |heap| then ThreadUnsound else
        var v := localState.get(localVar);
        var newHeap := HeapUpdate(heap, ref.reference, field, v);
        ThreadResult(newHeap, this.newHead(localState.next(statement.next)))
      case _ => ThreadResult(heap, this) // TODO
/*
      case AssignDeref(target, localVar, field)     // Requires localVar != null
      case IfEq(localVar, localVar2, thn, els)
      case Return(name)
      case AssignMethodCall(target, methodRef, argA, argB, argC)*/

    }
  }

  lemma EvaluateOnVerifiedNeverUnsound(codeState: CodeState, heap: Heap)
    requires codeState.Verified()
    requires this.Verified(codeState, heap)
    ensures this.Evaluate(codeState, heap) != ThreadUnsound
    ensures 
      var ThreadResult(newHeap, newMethodStack) := this.Evaluate(codeState, heap);
      newMethodStack.Verified(codeState, newHeap)
  {
    if StackNil? {
      return;
    }
    var localState := head;
    var statement := localState.statement;
    match statement {
      case AssignConst(target, value, next) =>
        return;
      case AssignRef(target, field, localVar, next) =>
        var ref := localState.get(target);
        assert ref.LocalValueRef? && ref.reference < |heap|;
        var v := localState.get(localVar);
        var newHeap := heap[ref.reference := heap[ref.reference].assign(field, v)];
        var newMethodStack := this.newHead(localState.next(statement.next));
        assert newMethodStack.tail.Verified(codeState, heap);
        newMethodStack.tail.VerifiedDoesNotChangeOnHeapUpdate(codeState, heap, ref.reference, field, v);
        assert newMethodStack.tail.Verified(codeState, newHeap);
        assert newMethodStack.Verified(codeState, newHeap);
        return;
      case _ =>
        return;
    }
  }
}

type StructVal(==,!new) {
  function assign(field: Field, newValue: Value): StructVal
}

// Program state at compilation time
datatype ProgramState = Unsound |
  ProgramState(codeState: CodeState, heap: Heap, thread1: MethodStack, thread2: MethodStack)
{
  ghost predicate Verified() {
    && !Unsound? && codeState.Verified()
    && thread1.Verified(codeState, heap)
    && thread2.Verified(codeState, heap)
   }
  function Evaluate(rng: RNG): (ProgramState, RNG)
  {
    if Unsound? then (Unsound, rng) else
    var (choice, rng1) := randomBool(rng);
    if choice then
      var result := thread1.Evaluate(codeState, heap);
      if result == ThreadUnsound then (Unsound, rng1) else
      (ProgramState(codeState, result.heap, result.state, thread2), rng1)
    else
      var result := thread2.Evaluate(codeState, heap);
      if result == ThreadUnsound then (Unsound, rng1) else
      (ProgramState(codeState, result.heap, thread1, result.state), rng1)
  }
}

lemma EvaluateOnVerifiedNeverUnsound(state: ProgramState, rng: RNG)
  requires state.Verified()
  ensures state.Evaluate(rng).0 != Unsound
  ensures state.Evaluate(rng).0.Verified()
{
  var (choice, rng1) := randomBool(rng);
  if choice {
    state.thread1.EvaluateOnVerifiedNeverUnsound(state.codeState, state.heap);
  } else {
    state.thread2.EvaluateOnVerifiedNeverUnsound(state.codeState, state.heap);
  }
}
  
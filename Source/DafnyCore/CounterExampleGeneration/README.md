# Counterexample Generation

The following is a class-by-class description of the files in this directory intended to help with maintaining and improving the counterexample generation feature of Dafny:

- [DafnyModel](DafnyModel.cs) - a wrapper around Boogie's `Model` class that defines Dafny specific functions and provides functionality for extracting types and values of `Elements` representing Dafny variables. The three core methods are:
  - `GetDafnyType`, which returns a `DafnyModelType` instance for an arbitrary `Element` in the underlying model
  - `CanonicalName`, which returns the value of any Element representing a variable of the basic type in Dafny
  - `GetExpansion`, which computes all the "children" of a particular variable, that is fields for objects, destructor values for datatypes, elements for sequences, etc.
- [DafnyModelState](DafnyModelState.cs) - Represents a state in a `DafnyModel` and captures the values of all variables at a particular point in the code.
- [DafnyModelVariable](DafnyModelVariable.cs) - Represents a variable at a particular state. Note that a variable in Dafny source can be represented by multiple `DafnyModelVariables`, one for each `DafnyModelState` in `DafnyModel`. The subclasses of `DafnyModelVariable` are:
  - `DuplicateVariable` - a variable that has a different name but represents the same `Element` in the same `DafnyModelState` as some other variable.
  - `MapVariable` - a variable that represents a map. Allows adding mappings to the map and displaying the map using Dafny syntax.
  - `SeqVariable` - a variable that represents a sequence. Allows displaying the sequence using Dafny syntax.
- [DafnyModelVariableFactory](DafnyModelVariable.cs) - A static class for generating instance of `DafnyModelvariable` and its subclasses. The factory chooses which subclass of `DafnyModelVariable` to employ depending on the `Microsoft.Dafny.Type` of the `Element` for which the variable is generated.
- [DafnyModelType](DafnyModelTypeUtils.cs) - Contains a set of utils for manipulating type objects (e.g. reconstructing the original Dafny type name from its Boogie translation: `Mo_dule_.Module2_.Cla__ss` from `Mo__dule___mModule2__.Cla____ss`).

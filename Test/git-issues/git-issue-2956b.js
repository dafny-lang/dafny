// The JS compiler would normally convert this integer value to a BigNumber.
// Omitting the conversion tests an edge case that would not arise during normal compilation.
global.OneOne = () => _dafny.Seq.of(1);

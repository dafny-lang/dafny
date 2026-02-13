// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
#nullable enable

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.BaseTypes;
using Microsoft.Boogie;

namespace Microsoft.Dafny {

  /// <summary>
  /// A wrapper around Boogie's Model class that allows extracting
  /// types and values of Elements representing Dafny variables. The three core
  /// methods are: GetDafnyType, DatatypeConstructorName, and GetExpansion
  /// </summary>
  public class DafnyModel {
    public readonly List<string> LoopGuards;
    private readonly DafnyOptions options;
    public readonly Model Model;
    public readonly List<PartialState> States = [];
    public static readonly UserDefinedType UnknownType =
      new(new Token(), "?", null);
    private readonly ModelFuncWrapper fSelect, fSetMember, fSeqLength, fSeqIndex, fBox,
      fDim, fIndexField, fMultiIndexField, fDtype, fCharToInt, fTag, fBv,
      fNull, fSetUnion, fSetIntersection, fSetDifference, fSetUnionOne,
      fSetEmpty, fSeqEmpty, fSeqBuild, fSeqAppend, fSeqDrop, fSeqTake,
      fSeqUpdate, fSeqCreate, fU2Real, fU2Bool, fU2Int,
      fMapDomain, fMapElements, fMapValues, fMapBuild, fMapEmpty, fIs, fIsBox, fUnbox, fLs, fLz;
    private readonly Dictionary<Model.Element, Model.FuncTuple> datatypeValues = new();
    private readonly List<Model.Func> bitvectorFunctions = [];

    // the model will begin assigning characters starting from this utf value
    private static readonly Regex UnderscoreRemovalRegex = new("__");

    // This set is used by GetDafnyType to prevent infinite recursion
    private HashSet<Model.Element> exploredElements = [];

    private readonly Dictionary<Model.Element, LiteralExpr> concretizedValues = new();

    public DafnyModel(Model model, DafnyOptions options) {
      Model = model;
      this.options = options;
      var tyArgMultiplier = options.TypeEncodingMethod switch {
        CoreOptions.TypeEncoding.Arguments => 1,
        _ => 0
      };
      fSelect = ModelFuncWrapper.MergeFunctions(this, ["MapType0Select", "MapType1Select"], 2);
      fSetMember = new ModelFuncWrapper(this, "Set#IsMember", 2, 0);
      fSeqLength = new ModelFuncWrapper(this, "Seq#Length", 1, 0);
      fSeqBuild = new ModelFuncWrapper(this, "Seq#Build", 2, 0);
      fSeqAppend = new ModelFuncWrapper(this, "Seq#Append", 2, 0);
      fSeqDrop = new ModelFuncWrapper(this, "Seq#Drop", 2, 0);
      fSeqTake = new ModelFuncWrapper(this, "Seq#Take", 2, 0);
      fSeqIndex = new ModelFuncWrapper(this, "Seq#Index", 2, 0);
      fSeqUpdate = new ModelFuncWrapper(this, "Seq#Update", 3, 0);
      fSeqCreate = new ModelFuncWrapper(this, "Seq#Create", 4, 0);
      fSeqEmpty = new ModelFuncWrapper(this, "Seq#Empty", 0, 0);
      fSetEmpty = new ModelFuncWrapper(this, "Set#Empty", 0, 0);
      fSetUnion = new ModelFuncWrapper(this, "Set#Union", 2, 0);
      fSetUnionOne = new ModelFuncWrapper(this, "Set#UnionOne", 2, 0);
      fSetIntersection = new ModelFuncWrapper(this, "Set#Intersection", 2, 0);
      fSetDifference = new ModelFuncWrapper(this, "Set#Difference", 2, 0);
      fMapDomain = new ModelFuncWrapper(this, "Map#Domain", 1, 0);
      fMapElements = new ModelFuncWrapper(this, "Map#Elements", 1, 0);
      fMapValues = new ModelFuncWrapper(this, "Map#Values", 1, 0);
      fMapBuild = new ModelFuncWrapper(this, "Map#Build", 3, 0);
      fMapEmpty = new ModelFuncWrapper(this, "Map#Empty", 0, 0);
      fIs = new ModelFuncWrapper(this, "$Is", 2, tyArgMultiplier);
      fIsBox = new ModelFuncWrapper(this, "$IsBox", 2, 0);
      fBox = new ModelFuncWrapper(this, BoogieGenerator.BoxFunctionName, 1, tyArgMultiplier);
      fDim = new ModelFuncWrapper(this, "FDim", 1, 0);
      fIndexField = new ModelFuncWrapper(this, "IndexField", 1, 0);
      fMultiIndexField = new ModelFuncWrapper(this, "MultiIndexField", 2, 0);
      fDtype = new ModelFuncWrapper(this, "dtype", 1, 0);
      fNull = new ModelFuncWrapper(this, "null", 0, 0);
      fCharToInt = new ModelFuncWrapper(this, "char#ToInt", 1, 0);
      fU2Real = new ModelFuncWrapper(this, "U_2_real", 1, 0);
      fU2Bool = new ModelFuncWrapper(this, "U_2_bool", 1, 0);
      fU2Int = new ModelFuncWrapper(this, "U_2_int", 1, 0);
      fTag = new ModelFuncWrapper(this, "Tag", 1, 0);
      fBv = new ModelFuncWrapper(this, "TBitvector", 1, 0);
      fUnbox = new ModelFuncWrapper(this, BoogieGenerator.UnboxFunctionName, 2, 0);
      fLs = new ModelFuncWrapper(this, "$LS", 1, 0);
      fLz = new ModelFuncWrapper(this, "$LZ", 0, 0);
      InitDataTypes();
      RegisterReservedBitVectors();
      LoopGuards = [];
      foreach (var s in model.States) {
        var sn = new PartialState(this, s);
        States.Add(sn);
        if (sn.IsLoopEntryState) {
          LoopGuards.Add("counterexampleLoopGuard" + LoopGuards.Count);
        }
        sn.LoopGuards = LoopGuards.ToList();
      }
    }

    public void AssignConcretePrimitiveValues() {
      bool isTrueReserved = false;
      foreach (var app in fU2Bool.Apps) {
        isTrueReserved |= ((Model.Boolean)app.Result).Value;
      }
      foreach (var element in Model.Elements) {
        var type = GetFormattedDafnyType(element);
        if (type is BoolType && GetLiteralExpression(element, type) == null) {
          if (isTrueReserved) {
            concretizedValues[element] = new LiteralExpr(Token.NoToken, false);
          } else {
            concretizedValues[element] = new LiteralExpr(Token.NoToken, true);
          }
          continue;
        }
        if (GetLiteralExpression(element, type) != null) {
          continue;
        }
        ModelFuncWrapper? otherValuesFunction = null;
        switch (type) {
          case BitvectorType bitvectorType: {
              var funcName = "U_2_bv" + bitvectorType.Width;
              if (Model.HasFunc(funcName)) {
                otherValuesFunction = new ModelFuncWrapper(Model.GetFunc(funcName), 0);
              }
              break;
            }
          case CharType:
            otherValuesFunction = fCharToInt;
            break;
          case RealType:
            otherValuesFunction = fU2Real;
            break;
          case IntType:
            otherValuesFunction = fU2Int;
            break;
          default:
            continue;
        }
        var reservedValues = otherValuesFunction!.Apps
          .Select(app => GetLiteralExpression(app.Result, type))
          .OfType<Expression>()
          .Select(literal => literal.ToString()).ToHashSet();
        reservedValues.UnionWith(concretizedValues.Values.Select(literal => literal.ToString()));
        int numericalValue = -1;
        LiteralExpr? literal = null;
        bool literalIsReserved = true;
        while (literalIsReserved) {
          numericalValue++;
          switch (type) {
            case BitvectorType:
            case IntType: {
                literal = new LiteralExpr(Token.NoToken, BigInteger.Parse(numericalValue.ToString()));
                break;
              }
            case CharType:
              literal = new CharLiteralExpr(Token.NoToken, PrettyPrintChar(numericalValue));
              break;
            case RealType:
              literal = new LiteralExpr(Token.NoToken, BigDec.FromString(numericalValue.ToString()));
              break;
          }
          if (!reservedValues.Contains(literal!.ToString())) {
            literalIsReserved = false;
          }
        }
        concretizedValues[element] = literal!;
      }
    }

    /// <summary>
    /// Extract and parse the first Dafny model recorded in the model view file.
    /// </summary>
    public static DafnyModel ExtractModel(DafnyOptions options, string mv) {
      const string begin = "*** MODEL";
      const string end = "*** END_MODEL";
      int beginIndex = mv.IndexOf(begin, StringComparison.Ordinal);
      int endIndex = mv.IndexOf(end, StringComparison.Ordinal);
      var modelString = mv.Substring(beginIndex, endIndex + end.Length - beginIndex);
      var model = Model.ParseModels(new StringReader(modelString)).First();
      return new DafnyModel(model, options);
    }

    public override string ToString() {
      var result = new StringBuilder();
      AssignConcretePrimitiveValues();
      result.AppendLine("WARNING: the following counterexample may be inconsistent or invalid. See dafny.org/dafny/DafnyRef/DafnyRef#sec-counterexamples");
      if (LoopGuards.Count > 0) {
        result.AppendLine("Temporary variables to describe counterexamples: ");
        foreach (var loopGuard in LoopGuards) {
          result.AppendLine($"ghost var {loopGuard} : bool := false;");
        }
      }
      foreach (var state in States.Where(state => state.StateContainsPosition())) {
        result.AppendLine(state.FullStateName + ":");
        result.AppendLine(state.AsAssumption().ToString());
      }
      return result.ToString();
    }

    /// <summary>
    /// Collect the array dimensions from the various array.Length functions,
    /// and collect all known datatype values
    /// </summary>
    private void InitDataTypes() {
      const string datatypeConstructorPrefix = "#";
      const string reservedVariablePrefix = "##";
      const string accessorString = ".";
      foreach (var fn in Model.Functions) {
        if (fn.Name.StartsWith(datatypeConstructorPrefix) &&
            !fn.Name.StartsWith(reservedVariablePrefix) &&
            fn.Name.Contains(accessorString)) {
          foreach (var tpl in fn.Apps) {
            var elt = tpl.Result;
            datatypeValues[elt] = tpl;
          }
        }
      }
    }

    /// <summary>
    /// Return the character representation of a UTF code understood by Dafny
    /// This is either the character itself, if it is a parsable ASCII,
    /// Escaped character, for the cases specified in Dafny manual,
    /// Or escaped UTF code otherwise
    /// </summary>
    private static string PrettyPrintChar(int utfCode) {
      switch (utfCode) {
        case 0:
          return "\\0";
        case 9:
          return "\\t";
        case 10:
          return "\\n";
        case 13:
          return "\\r";
        case 34:
          return "\\\"";
        case 39:
          return "\\\'";
        case 92:
          return "\\\\";
        default:
          if (utfCode is >= 32 and <= 126) {
            return $"{Convert.ToChar(utfCode)}";
          }
          return $"\\U{{{utfCode:X4}}}";
      }
    }

    /// <summary> Registered all bv values specified by the model </summary>
    private void RegisterReservedBitVectors() {
      var bvFuncName = new Regex("^U_2_bv[0-9]+$");
      foreach (var func in Model.Functions) {
        if (!bvFuncName.IsMatch(func.Name)) {
          continue;
        }
        bitvectorFunctions.Add(func);
      }
    }

    /// <summary>
    /// Return the name of a 0-arity type function that maps to the element if such
    /// a function exists and is unique. Return null otherwise.
    /// </summary>
    private static string? GetTrueTypeName(Model.Element element) {
      return element.Names.FirstOrDefault(funcTuple => funcTuple.Func.Arity == 0)?.Func.Name;
    }

    /// <summary> Get the Dafny type of an element </summary>
    internal Type GetFormattedDafnyType(Model.Element element) {
      exploredElements = [];
      return DafnyModelTypeUtils.GetInDafnyFormat(GetDafnyType(element));
    }

    internal void AddTypeConstraints(PartialValue partialValue) {
      foreach (var typeElement in GetIsResults(partialValue.Element)) {
        var reconstructedType = DafnyModelTypeUtils.GetInDafnyFormat(ReconstructType(typeElement));
        if (reconstructedType.ToString() != partialValue.Type.ToString()) {
          var _ = new TypeTestConstraint(partialValue, reconstructedType);
        }
      }
    }

    /// <summary> Get the Dafny type of an element </summary>
    private Type GetDafnyType(Model.Element element) {
      if (exploredElements.Contains(element)) {
        return UnknownType;
      }
      exploredElements.Add(element);
      switch (element.Kind) {
        case Model.ElementKind.Boolean:
          return Type.Bool;
        case Model.ElementKind.Integer:
          return Type.Int;
        case Model.ElementKind.Real:
          return Type.Real;
        case Model.ElementKind.BitVector:
          return new BitvectorType(options, ((Model.BitVector)element).Size);
        case Model.ElementKind.Uninterpreted:
          return GetDafnyType((element as Model.Uninterpreted)!);
        case Model.ElementKind.DataValue:
          if (((Model.DatatypeValue)element).ConstructorName is "-" or "/") {
            return GetDafnyType(
              ((Model.DatatypeValue)element).Arguments.First());
          }
          return UnknownType;
        default:
          return UnknownType;
      }
    }

    /// <summary>
    /// Return all elements x that satisfy ($Is element x)
    /// </summary>
    private List<Model.Element> GetIsResults(Model.Element element) {
      List<Model.Element> result = [];
      foreach (var tuple in fIs.AppsWithArg(0, element)) {
        if (((Model.Boolean)tuple.Result).Value) {
          result.Add(tuple.Args[1]);
        }
      }
      return result;
    }

    private Expression? GetLiteralExpression(Model.Element element, Type type) {
      var result = GetLiteralExpressionHelper(element, type);
      if (concretizedValues.ContainsKey(element) && result == null) {
        result = concretizedValues[element];
      }
      if (result != null) {
        result.Type = type;
      }
      return result;
    }

    /// <summary>
    /// If the provided <param name="element"></param> represents a literal in Dafny, return that literal.
    /// Otherwise, return null.
    /// </summary>
    private Expression? GetLiteralExpressionHelper(Model.Element element, Type type) {
      if (Equals(element, fNull.GetConstant())) {
        return new LiteralExpr(Token.NoToken);
      }

      if (element is not Model.Real && element is Model.Number number) {
        return new LiteralExpr(Token.NoToken, BigInteger.Parse(number.Numeral));
      }

      if (element is Model.Real real) {
        return new LiteralExpr(Token.NoToken, BigDec.FromString(real.ToString()));
      }

      if (element is Model.Boolean boolean) {
        return new LiteralExpr(Token.NoToken, boolean.Value);
      }

      if (element.Kind == Model.ElementKind.DataValue) {
        var datatypeValue = (Model.DatatypeValue)element;
        switch (datatypeValue.ConstructorName) {
          case "-":
            return new NegationExpression(Token.NoToken,
              GetLiteralExpression(datatypeValue.Arguments.First(), type)!);
          case "/":
            return new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Div,
              GetLiteralExpression(datatypeValue.Arguments[0], type),
              GetLiteralExpression(datatypeValue.Arguments[1], type));
        }
      }

      var unboxedValue = fU2Int.OptEval(element);
      unboxedValue ??= fU2Bool.OptEval(element);
      unboxedValue ??= fU2Real.OptEval(element);
      if (unboxedValue != null) {
        return GetLiteralExpression(unboxedValue, type);
      }

      if (fCharToInt.OptEval(element) is Model.Integer literalCharValue) {
        if (int.TryParse(literalCharValue.Numeral,
              out var utfCode) && utfCode is <= char.MaxValue and >= 0) {
          return new CharLiteralExpr(Token.NoToken, PrettyPrintChar(utfCode));
        }
      }

      foreach (var bitvectorFunction in bitvectorFunctions) {
        if (bitvectorFunction.OptEval(element) is Model.Number literalBitVectorValur) {
          return new LiteralExpr(Token.NoToken,
            BigInteger.Parse(literalBitVectorValur.Numeral));
        }
      }

      return null;
    }

    public void GetExpansion(PartialState state, PartialValue value) {
      var literalExpr = GetLiteralExpression(value.Element, value.Type);
      if (literalExpr != null) {
        var _ = new LiteralExprConstraint(value, literalExpr);
        return;
      }

      if (value.Nullable) {
        var _ = new NotNullConstraint(value);
      }

      if (value.Type is BitvectorType || value.Type is CharType || value.Type is RealType || value.Type is BoolType || value.Type is IntType) {
        foreach (var element in Model.Elements.Where(element => !Equals(element, value.Element))) {
          var elementType = GetFormattedDafnyType(element);
          if (elementType.ToString() == value.Type.ToString()) {
            var partialValue = PartialValue.Get(element, state);
            var _ = new NeqConstraint(value, partialValue);
          }
        }
        return;
      }

      var valueIsDatatype = datatypeValues.TryGetValue(value.Element, out var fnTuple);

      var layerValue = fLz.GetConstant();
      while (layerValue != null && fLs.AppWithArg(0, layerValue) != null && !Equals(fLs.AppWithArg(0, layerValue)!.Result, fLz.GetConstant())) {
        layerValue = fLs.AppWithArg(0, layerValue)!.Result;
      }
      var functionApplications = GetFunctionConstants(value.Element, layerValue);
      foreach (var functionApplication in functionApplications) {
        var result = PartialValue.Get(functionApplication.Result, state);
        var args = functionApplication.Args.Select(arg => PartialValue.Get(arg, state)).ToList();
        args = Equals(functionApplication.Args[0], layerValue) ? args.Skip(2).ToList() : args.Skip(1).ToList();
        var _ = new FunctionCallConstraint(result, value, args, functionApplication.Func.Name.Split(".").Last(), !valueIsDatatype);
      }

      if (valueIsDatatype) {
        var __ = new DatatypeConstructorCheckConstraint(value, fnTuple!.Func.Name.Split(".").Last());
        // Elt is a datatype value
        var destructors = GetDestructorFunctions(value.Element).OrderBy(f => f.Name).ToList();
        if (destructors.Count > fnTuple.Args.Length) {
          // Try to filter out predicate functions
          // (that follow a format very similar to that of destructor names)
          destructors = destructors.Where(destructor =>
              fnTuple.Args.Any(arg => Equals(destructor.OptEval(value.Element), arg)))
            .ToList();
        }

        var elements = new List<PartialValue>();
        if (destructors.Count == fnTuple.Args.Length) {
          // we know all destructor names
          foreach (var func in destructors) {
            if (func.OptEval(value.Element) is not { } modelElement) {
              continue;
            }
            var element = PartialValue.Get(UnboxNotNull(modelElement), state);
            elements.Add(element);
            var elementName = UnderscoreRemovalRegex.Replace(func.Name.Split(".").Last(), "_");
            var _ = new MemberSelectExprDatatypeConstraint(element, value, elementName);
          }
        } else {
          // we don't know destructor names, so we use indices instead
          for (int i = 0; i < fnTuple.Args.Length; i++) {
            var element = PartialValue.Get(UnboxNotNull(fnTuple.Args[i]), state);
            elements.Add(element);
          }
        }
        var ___ = new DatatypeValueConstraint(value, value.Type.ToString(), fnTuple.Func.Name.Split(".").Last(), elements);
        return;
      }

      switch (value.Type) {
        case SeqType: {
            if (fSeqEmpty.AppWithResult(value.Element) != null) {
              var _ = new LiteralExprConstraint(value, new SeqDisplayExpr(Token.NoToken, []));
              return;
            }
            var lenghtTuple = fSeqLength.AppWithArg(0, value.Element);
            BigNum seqLength = BigNum.MINUS_ONE;
            if (lenghtTuple != null) {
              var lengthValue = PartialValue.Get(lenghtTuple.Result, state);
              var lengthValueLiteral = GetLiteralExpression(lengthValue.Element, lengthValue.Type);
              if (lengthValueLiteral != null) {
                BigNum.TryParse(lengthValueLiteral.ToString(), out seqLength);
              }
              var _ = new CardinalityConstraint(lengthValue, value);
            }

            // Sequences can be constructed with the build operator:
            List<PartialValue> elements = [];

            Model.Element substring = value.Element;
            while (fSeqBuild.AppWithResult(substring) != null) {
              elements.Insert(0, PartialValue.Get(UnboxNotNull(fSeqBuild.AppWithResult(substring)!.Args[1]), state));
              substring = fSeqBuild.AppWithResult(substring)!.Args[0];
            }

            for (int i = 0; i < elements.Count; i++) {
              var index = new LiteralExpr(Token.NoToken, i) {
                Type = Type.Int
              };
              var _ = new SeqSelectExprWithLiteralConstraint(elements[i], value, index);
            }

            if (elements.Count == 0) {
              foreach (var funcTuple in fSeqIndex.AppsWithArg(0, value.Element)) {
                var elementId = PartialValue.Get(funcTuple.Args[1], state);
                var elementIdTry = GetLiteralExpression(funcTuple.Args[1], Type.Int);
                if (elementIdTry != null && elementIdTry.ToString().Contains("-")) {
                  continue;
                }
                if (elementIdTry != null && BigNum.TryParse(elementIdTry.ToString(), out var elementIdTryBigNum)) {
                  if (!seqLength.Equals(BigNum.MINUS_ONE) && !(elementIdTryBigNum - seqLength).IsNegative) {
                    continue; // element out of bounds for sequence
                  }
                }
                var element = PartialValue.Get(UnboxNotNull(funcTuple.Result), state);
                var _ = new SeqSelectExprConstraint(element, value, elementId);
              }
            } else {
              var _ = new SeqDisplayConstraint(value, elements);
            }

            return;
          }
        case SetType: {
            if (fMapDomain.AppsWithResult(value.Element).Any()) {
              foreach (var map in fMapDomain.AppsWithResult(value.Element)) {
                var mapValue = PartialValue.Get(map.Args[0], state);
                var _ = new MemberSelectExprDatatypeConstraint(value, mapValue, "Keys");
              }
              return;
            }
            if (fMapValues.AppsWithResult(value.Element).Any()) {
              foreach (var map in fMapValues.AppsWithResult(value.Element)) {
                var mapValue = PartialValue.Get(map.Args[0], state);
                var _ = new MemberSelectExprDatatypeConstraint(value, mapValue, "Values");
              }
            }
            if (fSetEmpty.AppWithResult(value.Element) != null) {
              var _ = new LiteralExprConstraint(value, new SetDisplayExpr(Token.NoToken, true, []));
              return;
            }

            foreach (var tpl in fSetMember.AppsWithArg(0, value.Element)) {
              var setElement = PartialValue.Get(UnboxNotNull(tpl.Args[1]), state);
              var containment = tpl.Result;
              if (containment is Model.Boolean boolean) {
                var _ = new ContainmentConstraint(setElement, value, boolean.Value);
              }
            }

            return;
          }
        case MapType: {
            var mapKeysAdded = new HashSet<Model.Element>(); // prevents mapping a key to multiple values
            var mapsElementsVisited = new HashSet<Model.Element>(); // prevents infinite recursion
            var current = value.Element;
            var mapBuilds = fMapBuild.AppsWithResult(current).ToList();
            var result = new List<PartialValue>();
            while (mapBuilds.Count != 0) {
              foreach (var mapBuild in mapBuilds.Where(m => Equals(m.Args[0], current))) {
                result.AddRange(AddMappingHelper(
                  state,
                  value,
                  Unbox(mapBuild.Args[1]),
                  Unbox(mapBuild.Args[2]),
                  mapKeysAdded));
              }

              mapsElementsVisited.Add(current);
              var nextMapBuild = mapBuilds.FirstOrDefault(m => !mapsElementsVisited.Contains(m.Args[0]));
              if (nextMapBuild == null) {
                return;
              }

              current = nextMapBuild.Args[0];
              mapBuilds = fMapBuild.AppsWithResult(nextMapBuild.Args[0])
                .Where(m => !mapsElementsVisited.Contains(m.Args[0])).ToList();
              result.AddRange(AddMappingHelper(
                state,
                value,
                Unbox(nextMapBuild.Args[1]),
                Unbox(nextMapBuild.Args[2]),
                mapKeysAdded));
            }

            var mapDomain = fMapDomain.OptEval(current);
            var mapElements = fMapElements.OptEval(current);
            if (mapDomain != null && mapElements != null) {
              foreach (var app in fSetMember.AppsWithArg(0, mapDomain)) {
                var valueElement = fSelect.OptEval(mapElements, app.Args[1]);
                if (valueElement != null) {
                  valueElement = Unbox(valueElement);
                }
                result.AddRange(AddMappingHelper(
                  state,
                  value,
                  Unbox(app.Args[1]),
                  valueElement,
                  mapKeysAdded, !((Model.Boolean)app.Result).Value));
              }
            }


            if (!result.Any() && fMapEmpty.AppWithResult(value.Element) != null) {
              var _ = new LiteralExprConstraint(value, new MapDisplayExpr(Token.NoToken, true, []));
            }

            return;

          }
        default: {

            var heap = state.State.TryGet("$Heap");
            // Elt is an array or an object:
            if (heap == null) {
              return;
            }

            var constantFields = GetDestructorFunctions(value.Element).OrderBy(f => f.Name).ToList();
            var fields = fSelect.AppsWithArgs(0, heap, 1, value.Element).ToList();

            foreach (var fieldFunc in constantFields) {
              if (fieldFunc.OptEval(value.Element) is not { } modelElement) {
                continue;
              }
              var field = PartialValue.Get(UnboxNotNull(modelElement), state);
              var fieldName = UnderscoreRemovalRegex.Replace(fieldFunc.Name.Split(".").Last(), "_");
              if (fieldName.Contains("#")) {
                continue;
              }
              var _ = new MemberSelectExprClassConstraint(field, value, fieldName);
            }

            if (!fields.Any()) {
              return;
            }

            foreach (var tpl in fSelect.AppsWithArg(0, fields.ToList()[0].Result)) {
              foreach (var fieldName in GetFieldNames(tpl.Args[1])) {
                if (fieldName != "alloc") {
                  var field = PartialValue.Get(UnboxNotNull(tpl.Result), state);
                  // make sure the field in quetion is not an array index
                  if (fieldName.Contains("#")) {
                    continue;
                  }
                  if (fieldName.StartsWith('[') && fieldName.EndsWith(']')) {
                    var indexStrings = fieldName.TrimStart('[').TrimEnd(']').Split(",");
                    var indices = new List<LiteralExpr>();
                    foreach (var indexString in indexStrings) {
                      if (BigInteger.TryParse(indexString, out var index)) {
                        var indexLiteral = new LiteralExpr(Token.NoToken, index);
                        indexLiteral.Type = Type.Int;
                        indices.Add(indexLiteral);
                      }
                    }
                    if (indices.Count != indexStrings.Length) {
                      continue;
                    }
                    var _ = new ArraySelectionConstraint(field, value, indices);
                  } else {
                    var _ = new MemberSelectExprClassConstraint(field, value, fieldName);
                  }
                }
              }
            }
            return;
          }
      }
    }

    /// <summary>
    /// Get the Dafny type of the value indicated by <param name="element"></param>
    /// This is in contrast to ReconstructType, which returns the type indicated by the element itself.
    /// This method tries to extract the base type (so sequence of characters instead of string)
    /// </summary>
    private Type GetDafnyType(Model.Uninterpreted element) {
      var finalResult = UnknownType;
      foreach (var typeElement in GetIsResults(element)) {
        var reconstructedType = ReconstructType(typeElement);
        if (reconstructedType is not UserDefinedType userDefinedType) {
          return reconstructedType;
        }
        if (finalResult.Name.EndsWith("?") || finalResult == UnknownType) {
          finalResult = userDefinedType;
        }
      }
      var seqOperation = fSeqAppend.AppWithResult(element);
      if (seqOperation != null && !exploredElements.Contains(seqOperation.Args[0])) { return GetDafnyType(seqOperation.Args[0]); }
      seqOperation = fSeqDrop.AppWithResult(element);
      if (seqOperation != null && !exploredElements.Contains(seqOperation.Args[0])) { return GetDafnyType(seqOperation.Args[0]); }
      seqOperation = fSeqTake.AppWithResult(element);
      if (seqOperation != null && !exploredElements.Contains(seqOperation.Args[0])) { return GetDafnyType(seqOperation.Args[0]); }
      seqOperation = fSeqUpdate.AppWithResult(element);
      if (seqOperation != null && !exploredElements.Contains(seqOperation.Args[0])) { return GetDafnyType(seqOperation.Args[0]); }
      seqOperation = fSeqBuild.AppWithResult(element);
      if (seqOperation != null && !exploredElements.Contains(UnboxNotNull(seqOperation.Args[1]))) { return new SeqType(GetDafnyType(UnboxNotNull(seqOperation.Args[1]))); }
      seqOperation = fSeqCreate.AppWithResult(element);
      if (seqOperation != null && !exploredElements.Contains(UnboxNotNull(seqOperation.Args.First()))) { return new SeqType(ReconstructType(seqOperation.Args.First())); }
      if (fSeqEmpty.AppWithResult(element) != null) { return new SeqType(null); }
      var setOperation = fSetUnion.AppWithResult(element);
      if (setOperation != null && !exploredElements.Contains(setOperation.Args[0])) { return GetDafnyType(setOperation.Args[0]); }
      setOperation = fSetIntersection.AppWithResult(element);
      if (setOperation != null && !exploredElements.Contains(setOperation.Args[0])) { return GetDafnyType(setOperation.Args[0]); }
      setOperation = fSetDifference.AppWithResult(element);
      if (setOperation != null && !exploredElements.Contains(setOperation.Args[0])) { return GetDafnyType(setOperation.Args[0]); }
      setOperation = fSetUnionOne.AppWithResult(element);
      if (setOperation != null && !exploredElements.Contains(setOperation.Args[1])) { return new SetType(true, GetDafnyType(UnboxNotNull(setOperation.Args[1]))); }
      if (fSetEmpty.AppWithResult(element) != null) { return new SetType(true, null); }
      var mapOperation = fMapBuild.AppWithResult(element);
      if (mapOperation != null) {
        return new MapType(true, GetDafnyType(UnboxNotNull(mapOperation.Args[1])), GetDafnyType(UnboxNotNull(mapOperation.Args[2])));
      }
      var unboxedTypes = fIsBox.AppsWithArg(0, element)
        .Where(tuple => ((Model.Boolean)tuple.Result).Value)
        .Select(tuple => tuple.Args[1]).ToList();
      if (unboxedTypes.Count == 1) {
        return ReconstructType(unboxedTypes[0]);
      }
      if (fCharToInt.OptEval(element) != null) {
        return Type.Char;
      }
      if (finalResult != UnknownType) {
        return finalResult;
      }
      var dtypeElement = fDtype.OptEval(element);
      if (dtypeElement != null) {
        ReconstructType(dtypeElement);
      }
      if (datatypeValues.TryGetValue(element, out var fnTuple)) {
        var fullyQualifiedPath = fnTuple.Func.Name[1..].Split(".");
        return new UserDefinedType(Token.NoToken, string.Join(".", fullyQualifiedPath.Take(fullyQualifiedPath.Count() - 1)), null);
      }
      return finalResult;
    }

    /// <summary>
    /// Reconstruct Dafny type from an element that represents a type in Z3
    /// </summary>
    private Type ReconstructType(Model.Element? typeElement) {
      if (typeElement == null) {
        return UnknownType;
      }
      var fullName = GetTrueTypeName(typeElement);
      if (fullName is { Length: > 7 } && fullName[..7].Equals("Tclass.")) {
        return new UserDefinedType(new Token(), fullName[7..], null);
      }
      switch (fullName) {
        case "TInt":
          return Type.Int;
        case "TBool":
          return Type.Bool;
        case "TReal":
          return Type.Real;
        case "TChar":
          return Type.Char;
      }
      if (fBv.AppWithResult(typeElement) is { } tupleWrapper) {
        return new BitvectorType(options, ((Model.Integer)tupleWrapper.Args[0]).AsInt());
      }

      Type fallBackType = UnknownType; // to be returned in the event all else fails
      if (fullName != null) { // this means this is a type variable
        fallBackType = new UserDefinedType(new Token(), fullName, null);
      }
      var tagElement = fTag.OptEval(typeElement);
      if (tagElement == null) {
        return fallBackType;
      }
      var tagName = GetTrueTypeName(tagElement);
      if (tagName == null || (tagName.Length < 10 && tagName != "TagSeq" &&
                              tagName != "TagSet" &&
                              tagName != "TagBitVector" &&
                              tagName != "TagMap")) {
        return fallBackType;
      }
      var typeArgs = Model.GetFunc("T" + tagName.Substring(3))?.
        AppWithResult(typeElement)?.
        Args.Select(ReconstructType).ToList();
      if (typeArgs == null) {
        return new UserDefinedType(new Token(), tagName.Substring(9), null);
      }

      switch (tagName) {
        case "TagSeq":
          return new SeqType(typeArgs.First());
        case "TagMap":
          return new MapType(true, typeArgs[0], typeArgs[1]);
        case "TagSet":
          return new SetType(true, typeArgs.First());
        default:
          tagName = tagName.Substring(9);
          if (tagName.StartsWith("_System.___hFunc") ||
              tagName.StartsWith("_System.___hTotalFunc") ||
              tagName.StartsWith("_System.___hPartialFunc")) {
            return new ArrowType(new Token(), typeArgs.SkipLast(1).ToList(),
              typeArgs.Last());
          }
          return new UserDefinedType(new Token(), tagName, typeArgs);
      }
    }

    /// <summary>
    /// Perform operations necessary to add a mapping to a map variable,
    /// return newly created PartialValue objects
    /// </summary>
    private IEnumerable<PartialValue> AddMappingHelper(PartialState state, PartialValue? mapVariable, Model.Element? keyElement, Model.Element? valueElement, HashSet<Model.Element> keySet, bool keyNotPresent = false) {
      if (mapVariable == null || keyElement == null || keySet.Contains(keyElement)) {
        yield break;
      }
      var key = PartialValue.Get(keyElement, state);
      var opcode = keyNotPresent ? BinaryExpr.Opcode.NotIn : BinaryExpr.Opcode.In;
      var _ = new ContainmentConstraint(key, mapVariable, opcode == BinaryExpr.Opcode.In);
      // Note that it is possible for valueElement to not be null while the element is not present in the set!
      if (valueElement != null && !keyNotPresent) {
        var value = PartialValue.Get(valueElement, state);
        var __ = new MapSelectExprConstraint(value, mapVariable, key);
        yield return value;
      }
      keySet.Add(keyElement);
      yield return key;
    }

    /// <summary>
    /// Return all functions application relevant to an element. These can be:
    /// 1) destructor values of a datatype
    /// 2) constant fields of an object
    /// 3) function applications
    /// </summary>
    private List<Model.Func> GetDestructorFunctions(Model.Element element) {
      var possibleTypeIdentifiers = GetIsResults(element);
      if (fDtype.OptEval(element) != null) {
        possibleTypeIdentifiers.Add(fDtype.OptEval(element)!);
      }
      var possiblyNullableTypes = possibleTypeIdentifiers
        .Select(ReconstructType).OfType<UserDefinedType>()
        .Where(type => type.Name != UnknownType.Name);
      var types = possiblyNullableTypes.Select(DafnyModelTypeUtils.GetNonNullable).OfType<UserDefinedType>().ToList();
      List<Model.Func> result = [];
      var builtInDatatypeDestructor = new Regex("^.*[^_](__)*_q$");
      var canCallFunctions = new HashSet<string>();
      foreach (var app in element.References) {
        if (app.Func.Arity != 1 || !Equals(app.Args[0], element) ||
            !types.Any(type => app.Func.Name.StartsWith(type.Name + ".")) ||
            builtInDatatypeDestructor.IsMatch(app.Func.Name.Split(".").Last()) ||
            app.Func.Name.Split(".").Last().StartsWith("_")) {
          continue;
        }

        if (app.Func.Name.EndsWith("#canCall")) {
          canCallFunctions.Add(app.Func.Name);
        } else {
          result.Add(app.Func);
        }
      }
      return result.Where(func => canCallFunctions.All(canCall => !canCall.StartsWith(func.Name))).ToList();
    }

    /// <summary>
    /// Return all function applications relevant to an element. 
    /// </summary>
    private List<Model.FuncTuple> GetFunctionConstants(Model.Element element, Model.Element? heap) {
      var possibleTypeIdentifiers = GetIsResults(element);
      if (fDtype.OptEval(element) != null) {
        possibleTypeIdentifiers.Add(fDtype.OptEval(element)!);
      }
      var possiblyNullableTypes = possibleTypeIdentifiers
        .Select(ReconstructType).OfType<UserDefinedType>()
        .Where(type => type.Name != UnknownType.Name);
      var types = possiblyNullableTypes.Select(DafnyModelTypeUtils.GetNonNullable).OfType<UserDefinedType>().ToList();
      List<Model.FuncTuple> applications = [];
      List<Model.FuncTuple> wellFormed = [];
      foreach (var app in element.References) {
        if (app.Args.Length == 0 || (!Equals(app.Args[0], element) && (heap == null || !Equals(app.Args[0], heap) || app.Args.Length == 1 || !Equals(app.Args[1], element))) ||
            !types.Any(type => app.Func.Name.StartsWith(type.Name + ".")) ||
            app.Func.Name.Split(".").Last().StartsWith("_")) {
          continue;
        }

        if (app.Func.Name.EndsWith("#canCall")) {
          if (app.Result is Model.Boolean { Value: true }) {
            wellFormed.Add(app);
          }
        } else {
          applications.Add(app);
        }
      }

      return applications.Where(application =>
        wellFormed.Any(wellFormedTuple => wellFormedTuple.Func.Name == application.Func.Name + "#canCall" &&
                                          ((wellFormedTuple.Args.Length == application.Args.Length &&
                                           wellFormedTuple.Args.SequenceEqual(application.Args)) ||
                                          (wellFormedTuple.Args.Length == application.Args.Length - 1 &&
                                           wellFormedTuple.Args.SequenceEqual(application.Args[1..]))))
      ).ToList();
    }

    /// <summary>
    /// Return the name of the field represented by the given element.
    /// Special care is required if the element represents an array index
    /// </summary>
    private List<string> GetFieldNames(Model.Element? elt) {
      if (elt == null) {
        return [];
      }
      var dims = fDim.OptEval(elt)?.AsInt();
      if (dims is null or 0) { // meaning elt is not an array index
        return elt.Names.Where(tuple =>
          tuple.Func.Arity == 0 && !tuple.Func.Name.Contains("$"))
          .Select(tuple => UnderscoreRemovalRegex
            .Replace(tuple.Func.Name.Split(".").Last(), "_"))
          .ToList();
      }
      // Reaching this code means elt is an index into an array
      var indices = new Model.Element?[(int)dims];
      for (int i = (int)dims; 0 <= --i;) {
        ModelFuncWrapper.ModelFuncTupleWrapper? dimTuple;
        if (i == 0) {
          dimTuple = fIndexField.AppWithResult(elt);
          if (dimTuple == null) {
            continue;
          }
          indices[i] = dimTuple.Args[0];
        } else {
          dimTuple = fMultiIndexField.AppWithResult(elt);
          if (dimTuple == null) {
            continue;
          }
          indices[i] = dimTuple.Args[1];
          elt = dimTuple.Args[0];
        }
      }
      return [
        "[" + string.Join(",",
          indices.ToList().ConvertAll(element => element == null ? "null" : element.ToString())) + "]"
      ];
    }

    /// <summary> Unboxes an element, if possible </summary>
    private Model.Element? Unbox(Model.Element? elt) {
      return elt == null ? null : UnboxNotNull(elt);
    }

    /// <summary> Unboxes an element, if possible </summary>
    private Model.Element UnboxNotNull(Model.Element elt) {
      var unboxed = fBox.AppWithResult(elt);
      if (unboxed != null) {
        return UnboxNotNull(unboxed.Args[0]);
      }
      unboxed = fUnbox.AppWithArg(1, elt);
      return unboxed != null ? UnboxNotNull(unboxed.Result) : elt;
    }
  }
}

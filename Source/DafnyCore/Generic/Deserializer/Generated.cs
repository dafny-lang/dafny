using System;
using System.Collections.Generic;

namespace Microsoft.Dafny {
  partial class Deserializer {
    public SourceOrigin ReadSourceOrigin() {
      var parameter0 = ReadToken();
      var parameter1 = ReadTokenOption();
      var parameter2 = ReadTokenOption();
      return new SourceOrigin(parameter0, parameter1, parameter2);
    }

    public SourceOrigin ReadSourceOriginOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadSourceOrigin();
    }

    public Name ReadName() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadString();
      return new Name(parameter0, parameter1);
    }

    public Name ReadNameOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadName();
    }

    public ModuleDefinition ReadModuleDefinition() {
      Microsoft.Dafny.ModuleDefinition parameter5 = null;
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadName();
      var parameter2 = ReadList<IOrigin>(() => ReadSourceOrigin());
      var parameter3 = ReadModuleKindEnum();
      var parameter4 = ReadImplementsOption();
      var parameter6 = ReadAttributesOption();
      var parameter7 = ReadList<TopLevelDecl>(() => ReadAbstract<TopLevelDecl>());
      return new ModuleDefinition(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
    }

    public ModuleDefinition ReadModuleDefinitionOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadModuleDefinition();
    }

    public UserDefinedType ReadUserDefinedType() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadAbstract<Expression>();
      return new UserDefinedType(parameter0, parameter1);
    }

    public UserDefinedType ReadUserDefinedTypeOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadUserDefinedType();
    }

    public LiteralExpr ReadLiteralExpr() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadAbstract<Object>();
      return new LiteralExpr(parameter0, parameter1);
    }

    public LiteralExpr ReadLiteralExprOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadLiteralExpr();
    }

    public Attributes ReadAttributes() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadString();
      var parameter2 = ReadList<Expression>(() => ReadAbstract<Expression>());
      var parameter3 = ReadAttributes();
      return new Attributes(parameter0, parameter1, parameter2, parameter3);
    }

    public Attributes ReadAttributesOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadAttributes();
    }

    public TypeParameter ReadTypeParameter() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadName();
      var parameter2 = ReadAttributesOption();
      var parameter3 = ReadTPVarianceSyntax();
      var parameter4 = ReadTypeParameterCharacteristics();
      var parameter5 = ReadList<Type>(() => ReadAbstract<Type>());
      return new TypeParameter(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5);
    }

    public TypeParameter ReadTypeParameterOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadTypeParameter();
    }

    public TypeParameterCharacteristics ReadTypeParameterCharacteristics() {
      return new TypeParameterCharacteristics();
    }

    public TypeParameterCharacteristics ReadTypeParameterCharacteristicsOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadTypeParameterCharacteristics();
    }

    private TPVarianceSyntax ReadTPVarianceSyntax() {
      int ordinal = ReadInt32();
      return (TPVarianceSyntax)ordinal;
    }

    public FrameExpression ReadFrameExpression() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadAbstract<Expression>();
      var parameter2 = ReadString();
      return new FrameExpression(parameter0, parameter1, parameter2);
    }

    public FrameExpression ReadFrameExpressionOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadFrameExpression();
    }

    public AttributedExpression ReadAttributedExpression() {
      var parameter0 = ReadAbstract<Expression>();
      var parameter1 = ReadAssertLabel();
      var parameter2 = ReadAttributesOption();
      return new AttributedExpression(parameter0, parameter1, parameter2);
    }

    public AttributedExpression ReadAttributedExpressionOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadAttributedExpression();
    }

    public Label ReadLabel() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadString();
      return new Label(parameter0, parameter1);
    }

    public Label ReadLabelOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadLabel();
    }

    public AssertLabel ReadAssertLabel() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadString();
      return new AssertLabel(parameter0, parameter1);
    }

    public AssertLabel ReadAssertLabelOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadAssertLabel();
    }

    public Formal ReadFormal() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadName();
      var parameter2 = ReadAbstract<Type>();
      var parameter4 = ReadBoolean();
      var parameter3 = ReadBoolean();
      var parameter5 = ReadAbstract<Expression>();
      var parameter6 = ReadAttributesOption();
      var parameter7 = ReadBoolean();
      var parameter8 = ReadBoolean();
      var parameter9 = ReadBoolean();
      var parameter10 = ReadStringOption();
      return new Formal(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10);
    }

    public Formal ReadFormalOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadFormal();
    }

    public Method ReadMethod() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadName();
      var parameter2 = ReadAttributesOption();
      var parameter3 = ReadBoolean();
      var parameter4 = ReadBoolean();
      var parameter5 = ReadList<TypeParameter>(() => ReadTypeParameter());
      var parameter6 = ReadList<Formal>(() => ReadFormal());
      var parameter7 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
      var parameter8 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
      var parameter9 = ReadSpecification<FrameExpression>();
      var parameter10 = ReadSpecification<Expression>();
      var parameter11 = ReadList<Formal>(() => ReadFormal());
      var parameter12 = ReadSpecification<FrameExpression>();
      var parameter13 = ReadBlockStmt();
      var parameter14 = ReadSourceOriginOption();
      var parameter15 = ReadBoolean();
      return new Method(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15);
    }

    public Method ReadMethodOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadMethod();
    }

    public AssertStmt ReadAssertStmt() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadAttributesOption();
      var parameter2 = ReadAbstract<Expression>();
      var parameter3 = ReadAssertLabelOption();
      return new AssertStmt(parameter0, parameter1, parameter2, parameter3);
    }

    public AssertStmt ReadAssertStmtOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadAssertStmt();
    }

    public BlockStmt ReadBlockStmt() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadAttributesOption();
      var parameter2 = ReadList<Statement>(() => ReadAbstract<Statement>());
      return new BlockStmt(parameter0, parameter1, parameter2);
    }

    public BlockStmt ReadBlockStmtOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadBlockStmt();
    }

    public Function ReadFunction() {
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadName();
      var parameter16 = ReadAttributes();
      var parameter2 = ReadBoolean();
      var parameter3 = ReadBoolean();
      var parameter5 = ReadList<TypeParameter>(() => ReadTypeParameter());
      var parameter6 = ReadList<Formal>(() => ReadFormal());
      var parameter9 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
      var parameter11 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
      var parameter10 = ReadSpecification<FrameExpression>();
      var parameter12 = ReadSpecification<Expression>();
      var parameter4 = ReadBoolean();
      var parameter7 = ReadFormal();
      var parameter8 = ReadAbstract<Type>();
      var parameter13 = ReadAbstractOption<Expression>();
      var parameter14 = ReadSourceOriginOption();
      var parameter15 = ReadBlockStmtOption();
      var parameter17 = ReadSourceOriginOption();
      return new Function(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15, parameter16, parameter17);
    }

    public Function ReadFunctionOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadFunction();
    }

    public ClassDecl ReadClassDecl() {
      Microsoft.Dafny.ModuleDefinition parameter4 = null;
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadName();
      var parameter2 = ReadAttributesOption();
      var parameter3 = ReadList<TypeParameter>(() => ReadTypeParameter());
      var parameter5 = ReadList<MemberDecl>(() => ReadAbstract<MemberDecl>());
      var parameter6 = ReadList<Type>(() => ReadAbstract<Type>());
      var parameter7 = ReadBoolean();
      return new ClassDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
    }

    public ClassDecl ReadClassDeclOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadClassDecl();
    }

    public LiteralModuleDecl ReadLiteralModuleDecl() {
      Microsoft.Dafny.DafnyOptions parameter0 = null;
      Microsoft.Dafny.ModuleDefinition parameter4 = null;
      var parameter1 = ReadSourceOrigin();
      var parameter2 = ReadName();
      var parameter3 = ReadAttributesOption();
      var parameter5 = ReadString();
      var parameter6 = ReadModuleDefinition();
      return new LiteralModuleDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6);
    }

    public LiteralModuleDecl ReadLiteralModuleDeclOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadLiteralModuleDecl();
    }

    public Implements ReadImplements() {
      var parameter0 = ReadImplementationKind();
      var parameter1 = ReadModuleQualifiedId();
      return new Implements(parameter0, parameter1);
    }

    public Implements ReadImplementsOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadImplements();
    }

    public ModuleQualifiedId ReadModuleQualifiedId() {
      var parameter0 = ReadList<Name>(() => ReadName());
      return new ModuleQualifiedId(parameter0);
    }

    public ModuleQualifiedId ReadModuleQualifiedIdOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadModuleQualifiedId();
    }

    private ImplementationKind ReadImplementationKind() {
      int ordinal = ReadInt32();
      return (ImplementationKind)ordinal;
    }

    private ModuleKindEnum ReadModuleKindEnum() {
      int ordinal = ReadInt32();
      return (ModuleKindEnum)ordinal;
    }

    public FileModuleDefinition ReadFileModuleDefinition() {
      Microsoft.Dafny.ModuleDefinition parameter5 = null;
      var parameter0 = ReadSourceOrigin();
      var parameter1 = ReadName();
      var parameter2 = ReadList<IOrigin>(() => ReadSourceOrigin());
      var parameter3 = ReadModuleKindEnum();
      var parameter4 = ReadImplementsOption();
      var parameter6 = ReadAttributesOption();
      var parameter7 = ReadList<TopLevelDecl>(() => ReadAbstract<TopLevelDecl>());
      return new FileModuleDefinition(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
    }

    public FileModuleDefinition ReadFileModuleDefinitionOption() {
      if (ReadBool()) {
        return default;
      }

      return ReadFileModuleDefinition();
    }

    private object ReadObject(System.Type actualType) {
      if (actualType == typeof(SourceOrigin)) {
        return ReadSourceOrigin();
      }

      if (actualType == typeof(Name)) {
        return ReadName();
      }

      if (actualType == typeof(ModuleDefinition)) {
        return ReadModuleDefinition();
      }

      if (actualType == typeof(UserDefinedType)) {
        return ReadUserDefinedType();
      }

      if (actualType == typeof(LiteralExpr)) {
        return ReadLiteralExpr();
      }

      if (actualType == typeof(Attributes)) {
        return ReadAttributes();
      }

      if (actualType == typeof(TypeParameter)) {
        return ReadTypeParameter();
      }

      if (actualType == typeof(TypeParameterCharacteristics)) {
        return ReadTypeParameterCharacteristics();
      }

      if (actualType == typeof(FrameExpression)) {
        return ReadFrameExpression();
      }

      if (actualType == typeof(AttributedExpression)) {
        return ReadAttributedExpression();
      }

      if (actualType == typeof(Label)) {
        return ReadLabel();
      }

      if (actualType == typeof(AssertLabel)) {
        return ReadAssertLabel();
      }

      if (actualType == typeof(Formal)) {
        return ReadFormal();
      }

      if (actualType == typeof(Method)) {
        return ReadMethod();
      }

      if (actualType == typeof(AssertStmt)) {
        return ReadAssertStmt();
      }

      if (actualType == typeof(BlockStmt)) {
        return ReadBlockStmt();
      }

      if (actualType == typeof(Function)) {
        return ReadFunction();
      }

      if (actualType == typeof(ClassDecl)) {
        return ReadClassDecl();
      }

      if (actualType == typeof(LiteralModuleDecl)) {
        return ReadLiteralModuleDecl();
      }

      if (actualType == typeof(Implements)) {
        return ReadImplements();
      }

      if (actualType == typeof(ModuleQualifiedId)) {
        return ReadModuleQualifiedId();
      }

      if (actualType == typeof(FileModuleDefinition)) {
        return ReadFileModuleDefinition();
      }

      throw new Exception();
    }
  }
}
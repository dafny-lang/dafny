// using System;
// using System.Collections.Generic;
//
// namespace Microsoft.Dafny {
//   partial class Deserializer {
//     public Name ReadName() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadString();
//       return new Name(parameter0, parameter1);
//     }
//
//     public Name ReadNameOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadName();
//     }
//
//     public ModuleDefinition ReadModuleDefinition() {
//       Microsoft.Dafny.ModuleDefinition parameter5 = null;
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadName();
//       var parameter2 = ReadList<IOrigin>(() => ReadAbstract<IOrigin>());
//       var parameter3 = ReadModuleKindEnum();
//       var parameter4 = ReadImplementsOption();
//       var parameter6 = ReadAttributesOption();
//       var parameter7 = ReadList<TopLevelDecl>(() => ReadAbstract<TopLevelDecl>());
//       return new ModuleDefinition(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
//     }
//
//     public ModuleDefinition ReadModuleDefinitionOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadModuleDefinition();
//     }
//
//     public UserDefinedType ReadUserDefinedType() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadAbstract<Expression>();
//       return new UserDefinedType(parameter0, parameter1);
//     }
//
//     public UserDefinedType ReadUserDefinedTypeOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadUserDefinedType();
//     }
//
//     public IdentifierExpr ReadIdentifierExpr() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadString();
//       return new IdentifierExpr(parameter0, parameter1);
//     }
//
//     public IdentifierExpr ReadIdentifierExprOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadIdentifierExpr();
//     }
//
//     public AutoGhostIdentifierExpr ReadAutoGhostIdentifierExpr() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadString();
//       return new AutoGhostIdentifierExpr(parameter0, parameter1);
//     }
//
//     public AutoGhostIdentifierExpr ReadAutoGhostIdentifierExprOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadAutoGhostIdentifierExpr();
//     }
//
//     public BinaryExpr ReadBinaryExpr() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadBinaryExprOpcode();
//       var parameter2 = ReadAbstract<Expression>();
//       var parameter3 = ReadAbstract<Expression>();
//       return new BinaryExpr(parameter0, parameter1, parameter2, parameter3);
//     }
//
//     public BinaryExpr ReadBinaryExprOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadBinaryExpr();
//     }
//
//     private BinaryExpr.Opcode ReadBinaryExprOpcode() {
//       int ordinal = ReadInt32();
//       return (BinaryExpr.Opcode)ordinal;
//     }
//
//     public LiteralExpr ReadLiteralExpr() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadAbstract<Object>();
//       return new LiteralExpr(parameter0, parameter1);
//     }
//
//     public LiteralExpr ReadLiteralExprOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadLiteralExpr();
//     }
//
//     public ITEExpr ReadITEExpr() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadBoolean();
//       var parameter2 = ReadAbstract<Expression>();
//       var parameter3 = ReadAbstract<Expression>();
//       var parameter4 = ReadAbstract<Expression>();
//       return new ITEExpr(parameter0, parameter1, parameter2, parameter3, parameter4);
//     }
//
//     public ITEExpr ReadITEExprOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadITEExpr();
//     }
//
//     public ApplySuffix ReadApplySuffix() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter2 = ReadAbstract<Expression>();
//       var parameter1 = ReadAbstractOption<IOrigin>();
//       var parameter3 = ReadActualBindings();
//       var parameter4 = ReadTokenOption();
//       return new ApplySuffix(parameter0, parameter1, parameter2, parameter3, parameter4);
//     }
//
//     public ApplySuffix ReadApplySuffixOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadApplySuffix();
//     }
//
//     public ActualBindings ReadActualBindings() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadList<ActualBinding>(() => ReadActualBinding());
//       return new ActualBindings(parameter0, parameter1);
//     }
//
//     public ActualBindings ReadActualBindingsOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadActualBindings();
//     }
//
//     public ActualBinding ReadActualBinding() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadAbstractOption<IOrigin>();
//       var parameter2 = ReadAbstract<Expression>();
//       var parameter3 = ReadBoolean();
//       return new ActualBinding(parameter0, parameter1, parameter2, parameter3);
//     }
//
//     public ActualBinding ReadActualBindingOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadActualBinding();
//     }
//
//     public NameSegment ReadNameSegment() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadString();
//       var parameter2 = ReadList<Type>(() => ReadAbstract<Type>());
//       return new NameSegment(parameter0, parameter1, parameter2);
//     }
//
//     public NameSegment ReadNameSegmentOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadNameSegment();
//     }
//
//     public IntType ReadIntType() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       return new IntType(parameter0);
//     }
//
//     public IntType ReadIntTypeOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadIntType();
//     }
//
//     public Attributes ReadAttributes() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadString();
//       var parameter2 = ReadList<Expression>(() => ReadAbstract<Expression>());
//       var parameter3 = ReadAttributes();
//       return new Attributes(parameter0, parameter1, parameter2, parameter3);
//     }
//
//     public Attributes ReadAttributesOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadAttributes();
//     }
//
//     public ExprRhs ReadExprRhs() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter2 = ReadAttributesOption();
//       var parameter1 = ReadAbstract<Expression>();
//       return new ExprRhs(parameter0, parameter1, parameter2);
//     }
//
//     public ExprRhs ReadExprRhsOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadExprRhs();
//     }
//
//     public TypeParameter ReadTypeParameter() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadName();
//       var parameter2 = ReadAttributesOption();
//       var parameter3 = ReadTPVarianceSyntax();
//       var parameter4 = ReadTypeParameterCharacteristics();
//       var parameter5 = ReadList<Type>(() => ReadAbstract<Type>());
//       return new TypeParameter(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5);
//     }
//
//     public TypeParameter ReadTypeParameterOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadTypeParameter();
//     }
//
//     public TypeParameterCharacteristics ReadTypeParameterCharacteristics() {
//       var parameter0 = ReadTypeParameterEqualitySupportValue();
//       var parameter1 = ReadTypeAutoInitInfo();
//       var parameter2 = ReadBoolean();
//       return new TypeParameterCharacteristics(parameter0, parameter1, parameter2);
//     }
//
//     public TypeParameterCharacteristics ReadTypeParameterCharacteristicsOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadTypeParameterCharacteristics();
//     }
//
//     private Type.AutoInitInfo ReadTypeAutoInitInfo() {
//       int ordinal = ReadInt32();
//       return (Type.AutoInitInfo)ordinal;
//     }
//
//     private TypeParameter.EqualitySupportValue ReadTypeParameterEqualitySupportValue() {
//       int ordinal = ReadInt32();
//       return (TypeParameter.EqualitySupportValue)ordinal;
//     }
//
//     private pbject ReadTPVarianceSyntax() {
//       throw new 
//     }
//
//     public FrameExpression ReadFrameExpression() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadAbstract<Expression>();
//       var parameter2 = ReadString();
//       return new FrameExpression(parameter0, parameter1, parameter2);
//     }
//
//     public FrameExpression ReadFrameExpressionOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadFrameExpression();
//     }
//
//     public AttributedExpression ReadAttributedExpression() {
//       var parameter0 = ReadAbstract<Expression>();
//       var parameter1 = ReadAssertLabelOption();
//       var parameter2 = ReadAttributesOption();
//       return new AttributedExpression(parameter0, parameter1, parameter2);
//     }
//
//     public AttributedExpression ReadAttributedExpressionOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadAttributedExpression();
//     }
//
//     public Label ReadLabel() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadString();
//       return new Label(parameter0, parameter1);
//     }
//
//     public Label ReadLabelOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadLabel();
//     }
//
//     public AssertLabel ReadAssertLabel() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadString();
//       return new AssertLabel(parameter0, parameter1);
//     }
//
//     public AssertLabel ReadAssertLabelOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadAssertLabel();
//     }
//
//     public Formal ReadFormal() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadName();
//       var parameter2 = ReadAbstract<Type>();
//       var parameter4 = ReadBoolean();
//       var parameter3 = ReadBoolean();
//       var parameter5 = ReadAbstractOption<Expression>();
//       var parameter6 = ReadAttributesOption();
//       var parameter7 = ReadBoolean();
//       var parameter8 = ReadBoolean();
//       var parameter9 = ReadBoolean();
//       var parameter10 = ReadStringOption();
//       return new Formal(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10);
//     }
//
//     public Formal ReadFormalOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadFormal();
//     }
//
//     public Method ReadMethod() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadName();
//       var parameter2 = ReadAttributesOption();
//       var parameter3 = ReadBoolean();
//       var parameter4 = ReadBoolean();
//       var parameter5 = ReadList<TypeParameter>(() => ReadTypeParameter());
//       var parameter6 = ReadList<Formal>(() => ReadFormal());
//       var parameter7 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
//       var parameter8 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
//       var parameter9 = ReadSpecification<FrameExpression>();
//       var parameter10 = ReadSpecification<Expression>();
//       var parameter11 = ReadList<Formal>(() => ReadFormal());
//       var parameter12 = ReadSpecification<FrameExpression>();
//       var parameter13 = ReadBlockStmt();
//       var parameter14 = ReadAbstractOption<IOrigin>();
//       var parameter15 = ReadBoolean();
//       return new Method(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15);
//     }
//
//     public Method ReadMethodOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadMethod();
//     }
//
//     public AssertStmt ReadAssertStmt() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadAttributesOption();
//       var parameter2 = ReadAbstract<Expression>();
//       var parameter3 = ReadAssertLabelOption();
//       return new AssertStmt(parameter0, parameter1, parameter2, parameter3);
//     }
//
//     public AssertStmt ReadAssertStmtOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadAssertStmt();
//     }
//
//     public ReturnStmt ReadReturnStmt() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter2 = ReadAttributesOption();
//       var parameter1 = ReadList<AssignmentRhs>(() => ReadAbstract<AssignmentRhs>());
//       return new ReturnStmt(parameter0, parameter1, parameter2);
//     }
//
//     public ReturnStmt ReadReturnStmtOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadReturnStmt();
//     }
//
//     public BlockStmt ReadBlockStmt() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadAttributesOption();
//       var parameter2 = ReadList<Statement>(() => ReadAbstract<Statement>());
//       return new BlockStmt(parameter0, parameter1, parameter2);
//     }
//
//     public BlockStmt ReadBlockStmtOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadBlockStmt();
//     }
//
//     public WhileStmt ReadWhileStmt() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter6 = ReadAttributesOption();
//       var parameter2 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
//       var parameter3 = ReadSpecification<Expression>();
//       var parameter4 = ReadSpecification<FrameExpression>();
//       var parameter5 = ReadBlockStmt();
//       var parameter1 = ReadAbstract<Expression>();
//       return new WhileStmt(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6);
//     }
//
//     public WhileStmt ReadWhileStmtOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadWhileStmt();
//     }
//
//     public IfStmt ReadIfStmt() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter5 = ReadAttributesOption();
//       var parameter1 = ReadBoolean();
//       var parameter2 = ReadAbstract<Expression>();
//       var parameter3 = ReadBlockStmt();
//       var parameter4 = ReadAbstractOption<Statement>();
//       return new IfStmt(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5);
//     }
//
//     public IfStmt ReadIfStmtOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadIfStmt();
//     }
//
//     public VarDeclStmt ReadVarDeclStmt() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter3 = ReadAttributesOption();
//       var parameter1 = ReadList<LocalVariable>(() => ReadLocalVariable());
//       var parameter2 = ReadAbstract<ConcreteAssignStatement>();
//       return new VarDeclStmt(parameter0, parameter1, parameter2, parameter3);
//     }
//
//     public VarDeclStmt ReadVarDeclStmtOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadVarDeclStmt();
//     }
//
//     public AssignStatement ReadAssignStatement() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter4 = ReadAttributesOption();
//       var parameter1 = ReadList<Expression>(() => ReadAbstract<Expression>());
//       var parameter2 = ReadList<AssignmentRhs>(() => ReadAbstract<AssignmentRhs>());
//       var parameter3 = ReadBoolean();
//       return new AssignStatement(parameter0, parameter1, parameter2, parameter3, parameter4);
//     }
//
//     public AssignStatement ReadAssignStatementOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadAssignStatement();
//     }
//
//     public LocalVariable ReadLocalVariable() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadString();
//       var parameter2 = ReadAbstract<Type>();
//       var parameter3 = ReadBoolean();
//       return new LocalVariable(parameter0, parameter1, parameter2, parameter3);
//     }
//
//     public LocalVariable ReadLocalVariableOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadLocalVariable();
//     }
//
//     public Function ReadFunction() {
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadName();
//       var parameter16 = ReadAttributesOption();
//       var parameter2 = ReadBoolean();
//       var parameter3 = ReadBoolean();
//       var parameter5 = ReadList<TypeParameter>(() => ReadTypeParameter());
//       var parameter6 = ReadList<Formal>(() => ReadFormal());
//       var parameter9 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
//       var parameter11 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
//       var parameter10 = ReadSpecification<FrameExpression>();
//       var parameter12 = ReadSpecification<Expression>();
//       var parameter4 = ReadBoolean();
//       var parameter7 = ReadFormalOption();
//       var parameter8 = ReadAbstract<Type>();
//       var parameter13 = ReadAbstractOption<Expression>();
//       var parameter14 = ReadAbstractOption<IOrigin>();
//       var parameter15 = ReadBlockStmtOption();
//       var parameter17 = ReadAbstractOption<IOrigin>();
//       return new Function(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15, parameter16, parameter17);
//     }
//
//     public Function ReadFunctionOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadFunction();
//     }
//
//     public ClassDecl ReadClassDecl() {
//       Microsoft.Dafny.ModuleDefinition parameter4 = null;
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadName();
//       var parameter2 = ReadAttributesOption();
//       var parameter3 = ReadList<TypeParameter>(() => ReadTypeParameter());
//       var parameter5 = ReadList<MemberDecl>(() => ReadAbstract<MemberDecl>());
//       var parameter6 = ReadList<Type>(() => ReadAbstract<Type>());
//       var parameter7 = ReadBoolean();
//       return new ClassDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
//     }
//
//     public ClassDecl ReadClassDeclOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadClassDecl();
//     }
//
//     public DefaultClassDecl ReadDefaultClassDecl() {
//       Microsoft.Dafny.ModuleDefinition parameter4 = null;
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadName();
//       var parameter2 = ReadAttributesOption();
//       var parameter3 = ReadList<TypeParameter>(() => ReadTypeParameter());
//       var parameter5 = ReadList<MemberDecl>(() => ReadAbstract<MemberDecl>());
//       var parameter6 = ReadList<Type>(() => ReadAbstract<Type>());
//       return new DefaultClassDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6);
//     }
//
//     public DefaultClassDecl ReadDefaultClassDeclOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadDefaultClassDecl();
//     }
//
//     public LiteralModuleDecl ReadLiteralModuleDecl() {
//       Microsoft.Dafny.DafnyOptions parameter0 = null;
//       Microsoft.Dafny.ModuleDefinition parameter4 = null;
//       var parameter1 = ReadAbstract<IOrigin>();
//       var parameter2 = ReadName();
//       var parameter3 = ReadAttributesOption();
//       var parameter5 = ReadString();
//       var parameter6 = ReadModuleDefinition();
//       return new LiteralModuleDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6);
//     }
//
//     public LiteralModuleDecl ReadLiteralModuleDeclOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadLiteralModuleDecl();
//     }
//
//     public Implements ReadImplements() {
//       var parameter0 = ReadImplementationKind();
//       var parameter1 = ReadModuleQualifiedId();
//       return new Implements(parameter0, parameter1);
//     }
//
//     public Implements ReadImplementsOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadImplements();
//     }
//
//     public ModuleQualifiedId ReadModuleQualifiedId() {
//       var parameter0 = ReadList<Name>(() => ReadName());
//       return new ModuleQualifiedId(parameter0);
//     }
//
//     public ModuleQualifiedId ReadModuleQualifiedIdOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadModuleQualifiedId();
//     }
//
//     private ImplementationKind ReadImplementationKind() {
//       int ordinal = ReadInt32();
//       return (ImplementationKind)ordinal;
//     }
//
//     private ModuleKindEnum ReadModuleKindEnum() {
//       int ordinal = ReadInt32();
//       return (ModuleKindEnum)ordinal;
//     }
//
//     public FileModuleDefinition ReadFileModuleDefinition() {
//       Microsoft.Dafny.ModuleDefinition parameter5 = null;
//       var parameter0 = ReadAbstract<IOrigin>();
//       var parameter1 = ReadName();
//       var parameter2 = ReadList<IOrigin>(() => ReadAbstract<IOrigin>());
//       var parameter3 = ReadModuleKindEnum();
//       var parameter4 = ReadImplementsOption();
//       var parameter6 = ReadAttributesOption();
//       var parameter7 = ReadList<TopLevelDecl>(() => ReadAbstract<TopLevelDecl>());
//       return new FileModuleDefinition(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
//     }
//
//     public FileModuleDefinition ReadFileModuleDefinitionOption() {
//       if (ReadIsNull()) {
//         return default;
//       }
//
//       return ReadFileModuleDefinition();
//     }
//
//     private object ReadObject(System.Type actualType) {
//       if (actualType == typeof(Name)) {
//         return ReadName();
//       }
//
//       if (actualType == typeof(ModuleDefinition)) {
//         return ReadModuleDefinition();
//       }
//
//       if (actualType == typeof(UserDefinedType)) {
//         return ReadUserDefinedType();
//       }
//
//       if (actualType == typeof(IdentifierExpr)) {
//         return ReadIdentifierExpr();
//       }
//
//       if (actualType == typeof(AutoGhostIdentifierExpr)) {
//         return ReadAutoGhostIdentifierExpr();
//       }
//
//       if (actualType == typeof(BinaryExpr)) {
//         return ReadBinaryExpr();
//       }
//
//       if (actualType == typeof(LiteralExpr)) {
//         return ReadLiteralExpr();
//       }
//
//       if (actualType == typeof(ITEExpr)) {
//         return ReadITEExpr();
//       }
//
//       if (actualType == typeof(ApplySuffix)) {
//         return ReadApplySuffix();
//       }
//
//       if (actualType == typeof(ActualBindings)) {
//         return ReadActualBindings();
//       }
//
//       if (actualType == typeof(ActualBinding)) {
//         return ReadActualBinding();
//       }
//
//       if (actualType == typeof(NameSegment)) {
//         return ReadNameSegment();
//       }
//
//       if (actualType == typeof(IntType)) {
//         return ReadIntType();
//       }
//
//       if (actualType == typeof(Attributes)) {
//         return ReadAttributes();
//       }
//
//       if (actualType == typeof(ExprRhs)) {
//         return ReadExprRhs();
//       }
//
//       if (actualType == typeof(TypeParameter)) {
//         return ReadTypeParameter();
//       }
//
//       if (actualType == typeof(TypeParameterCharacteristics)) {
//         return ReadTypeParameterCharacteristics();
//       }
//
//       if (actualType == typeof(FrameExpression)) {
//         return ReadFrameExpression();
//       }
//
//       if (actualType == typeof(AttributedExpression)) {
//         return ReadAttributedExpression();
//       }
//
//       if (actualType == typeof(Label)) {
//         return ReadLabel();
//       }
//
//       if (actualType == typeof(AssertLabel)) {
//         return ReadAssertLabel();
//       }
//
//       if (actualType == typeof(Formal)) {
//         return ReadFormal();
//       }
//
//       if (actualType == typeof(Method)) {
//         return ReadMethod();
//       }
//
//       if (actualType == typeof(AssertStmt)) {
//         return ReadAssertStmt();
//       }
//
//       if (actualType == typeof(ReturnStmt)) {
//         return ReadReturnStmt();
//       }
//
//       if (actualType == typeof(BlockStmt)) {
//         return ReadBlockStmt();
//       }
//
//       if (actualType == typeof(WhileStmt)) {
//         return ReadWhileStmt();
//       }
//
//       if (actualType == typeof(IfStmt)) {
//         return ReadIfStmt();
//       }
//
//       if (actualType == typeof(VarDeclStmt)) {
//         return ReadVarDeclStmt();
//       }
//
//       if (actualType == typeof(AssignStatement)) {
//         return ReadAssignStatement();
//       }
//
//       if (actualType == typeof(LocalVariable)) {
//         return ReadLocalVariable();
//       }
//
//       if (actualType == typeof(Function)) {
//         return ReadFunction();
//       }
//
//       if (actualType == typeof(ClassDecl)) {
//         return ReadClassDecl();
//       }
//
//       if (actualType == typeof(DefaultClassDecl)) {
//         return ReadDefaultClassDecl();
//       }
//
//       if (actualType == typeof(LiteralModuleDecl)) {
//         return ReadLiteralModuleDecl();
//       }
//
//       if (actualType == typeof(Implements)) {
//         return ReadImplements();
//       }
//
//       if (actualType == typeof(ModuleQualifiedId)) {
//         return ReadModuleQualifiedId();
//       }
//
//       if (actualType == typeof(FileModuleDefinition)) {
//         return ReadFileModuleDefinition();
//       }
//
//       throw new Exception();
//     }
//   }
// }
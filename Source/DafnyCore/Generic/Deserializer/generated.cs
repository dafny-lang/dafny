using System;
using System.Collections.Generic;

namespace Microsoft.Dafny
{
    partial class Deserializer
    {
        public SourceOrigin DeserializeSourceOrigin()
        {
            var parameter0 = DeserializeTokenOption();
            var parameter1 = DeserializeToken();
            var parameter2 = DeserializeToken();
            return new SourceOrigin(parameter0, parameter1, parameter2);
        }

        public SourceOrigin DeserializeSourceOriginOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeSourceOrigin();
        }

        public Name DeserializeName()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeString();
            return new Name(parameter0, parameter1);
        }

        public Name DeserializeNameOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeName();
        }

        public ModuleDefinition DeserializeModuleDefinition()
        {
            Microsoft.Dafny.ModuleDefinition parameter5 = null;
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeName();
            var parameter2 = DeserializeList<IOrigin>(() => DeserializeSourceOrigin());
            var parameter3 = DeserializeModuleKindEnum();
            var parameter4 = DeserializeImplementsOption();
            var parameter6 = DeserializeAttributesOption();
            var parameter7 = DeserializeList<TopLevelDecl>(() => DeserializeAbstract<TopLevelDecl>());
            return new ModuleDefinition(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
        }

        public ModuleDefinition DeserializeModuleDefinitionOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeModuleDefinition();
        }

        public UserDefinedType DeserializeUserDefinedType()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeAbstract<Expression>();
            return new UserDefinedType(parameter0, parameter1);
        }

        public UserDefinedType DeserializeUserDefinedTypeOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeUserDefinedType();
        }

        public LiteralExpr DeserializeLiteralExpr()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeAbstract<Object>();
            return new LiteralExpr(parameter0, parameter1);
        }

        public LiteralExpr DeserializeLiteralExprOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeLiteralExpr();
        }

        public Attributes DeserializeAttributes()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeString();
            var parameter2 = DeserializeList<Expression>(() => DeserializeAbstract<Expression>());
            var parameter3 = DeserializeAttributes();
            return new Attributes(parameter0, parameter1, parameter2, parameter3);
        }

        public Attributes DeserializeAttributesOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeAttributes();
        }

        public TypeParameter DeserializeTypeParameter()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeName();
            var parameter2 = DeserializeAttributesOption();
            var parameter3 = DeserializeTPVarianceSyntax();
            var parameter4 = DeserializeTypeParameterCharacteristics();
            var parameter5 = DeserializeList<Type>(() => DeserializeAbstract<Type>());
            return new TypeParameter(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5);
        }

        public TypeParameter DeserializeTypeParameterOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeTypeParameter();
        }

        public TypeParameterCharacteristics DeserializeTypeParameterCharacteristics()
        {
            return new TypeParameterCharacteristics();
        }

        public TypeParameterCharacteristics DeserializeTypeParameterCharacteristicsOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeTypeParameterCharacteristics();
        }

        private TPVarianceSyntax DeserializeTPVarianceSyntax()
        {
            int ordinal = DeserializeInt32();
            return (TPVarianceSyntax)ordinal;
        }

        public FrameExpression DeserializeFrameExpression()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeAbstract<Expression>();
            var parameter2 = DeserializeString();
            return new FrameExpression(parameter0, parameter1, parameter2);
        }

        public FrameExpression DeserializeFrameExpressionOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeFrameExpression();
        }

        public AttributedExpression DeserializeAttributedExpression()
        {
            var parameter0 = DeserializeAbstract<Expression>();
            var parameter1 = DeserializeAssertLabel();
            var parameter2 = DeserializeAttributesOption();
            return new AttributedExpression(parameter0, parameter1, parameter2);
        }

        public AttributedExpression DeserializeAttributedExpressionOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeAttributedExpression();
        }

        public Label DeserializeLabel()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeString();
            return new Label(parameter0, parameter1);
        }

        public Label DeserializeLabelOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeLabel();
        }

        public AssertLabel DeserializeAssertLabel()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeString();
            return new AssertLabel(parameter0, parameter1);
        }

        public AssertLabel DeserializeAssertLabelOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeAssertLabel();
        }

        public Formal DeserializeFormal()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeName();
            var parameter2 = DeserializeAbstract<Type>();
            var parameter4 = DeserializeBoolean();
            var parameter3 = DeserializeBoolean();
            var parameter5 = DeserializeAbstract<Expression>();
            var parameter6 = DeserializeAttributesOption();
            var parameter7 = DeserializeBoolean();
            var parameter8 = DeserializeBoolean();
            var parameter9 = DeserializeBoolean();
            var parameter10 = DeserializeStringOption();
            return new Formal(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10);
        }

        public Formal DeserializeFormalOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeFormal();
        }

        public Method DeserializeMethod()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeName();
            var parameter2 = DeserializeAttributesOption();
            var parameter3 = DeserializeBoolean();
            var parameter4 = DeserializeBoolean();
            var parameter5 = DeserializeList<TypeParameter>(() => DeserializeTypeParameter());
            var parameter6 = DeserializeList<Formal>(() => DeserializeFormal());
            var parameter7 = DeserializeList<AttributedExpression>(() => DeserializeAttributedExpression());
            var parameter8 = DeserializeList<AttributedExpression>(() => DeserializeAttributedExpression());
            var parameter9 = DeserializeSpecification<FrameExpression>();
            var parameter10 = DeserializeSpecification<Expression>();
            var parameter11 = DeserializeList<Formal>(() => DeserializeFormal());
            var parameter12 = DeserializeSpecification<FrameExpression>();
            var parameter13 = DeserializeBlockStmt();
            var parameter14 = DeserializeSourceOriginOption();
            var parameter15 = DeserializeBoolean();
            return new Method(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15);
        }

        public Method DeserializeMethodOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeMethod();
        }

        public AssertStmt DeserializeAssertStmt()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeAttributesOption();
            var parameter2 = DeserializeAbstract<Expression>();
            var parameter3 = DeserializeAssertLabelOption();
            return new AssertStmt(parameter0, parameter1, parameter2, parameter3);
        }

        public AssertStmt DeserializeAssertStmtOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeAssertStmt();
        }

        public BlockStmt DeserializeBlockStmt()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeAttributesOption();
            var parameter2 = DeserializeList<Statement>(() => DeserializeAbstract<Statement>());
            return new BlockStmt(parameter0, parameter1, parameter2);
        }

        public BlockStmt DeserializeBlockStmtOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeBlockStmt();
        }

        public Function DeserializeFunction()
        {
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeName();
            var parameter16 = DeserializeAttributes();
            var parameter2 = DeserializeBoolean();
            var parameter3 = DeserializeBoolean();
            var parameter5 = DeserializeList<TypeParameter>(() => DeserializeTypeParameter());
            var parameter6 = DeserializeList<Formal>(() => DeserializeFormal());
            var parameter9 = DeserializeList<AttributedExpression>(() => DeserializeAttributedExpression());
            var parameter11 = DeserializeList<AttributedExpression>(() => DeserializeAttributedExpression());
            var parameter10 = DeserializeSpecification<FrameExpression>();
            var parameter12 = DeserializeSpecification<Expression>();
            var parameter4 = DeserializeBoolean();
            var parameter7 = DeserializeFormal();
            var parameter8 = DeserializeAbstract<Type>();
            var parameter13 = DeserializeAbstractOption<Expression>();
            var parameter14 = DeserializeSourceOriginOption();
            var parameter15 = DeserializeBlockStmtOption();
            var parameter17 = DeserializeSourceOriginOption();
            return new Function(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15, parameter16, parameter17);
        }

        public Function DeserializeFunctionOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeFunction();
        }

        public ClassDecl DeserializeClassDecl()
        {
            Microsoft.Dafny.ModuleDefinition parameter4 = null;
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeName();
            var parameter2 = DeserializeAttributesOption();
            var parameter3 = DeserializeList<TypeParameter>(() => DeserializeTypeParameter());
            var parameter5 = DeserializeList<MemberDecl>(() => DeserializeAbstract<MemberDecl>());
            var parameter6 = DeserializeList<Type>(() => DeserializeAbstract<Type>());
            var parameter7 = DeserializeBoolean();
            return new ClassDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
        }

        public ClassDecl DeserializeClassDeclOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeClassDecl();
        }

        public LiteralModuleDecl DeserializeLiteralModuleDecl()
        {
            Microsoft.Dafny.DafnyOptions parameter0 = null;
            Microsoft.Dafny.ModuleDefinition parameter4 = null;
            var parameter1 = DeserializeSourceOrigin();
            var parameter2 = DeserializeName();
            var parameter3 = DeserializeAttributesOption();
            var parameter5 = DeserializeString();
            var parameter6 = DeserializeModuleDefinition();
            return new LiteralModuleDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6);
        }

        public LiteralModuleDecl DeserializeLiteralModuleDeclOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeLiteralModuleDecl();
        }

        public Implements DeserializeImplements()
        {
            var parameter0 = DeserializeImplementationKind();
            var parameter1 = DeserializeModuleQualifiedId();
            return new Implements(parameter0, parameter1);
        }

        public Implements DeserializeImplementsOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeImplements();
        }

        public ModuleQualifiedId DeserializeModuleQualifiedId()
        {
            var parameter0 = DeserializeList<Name>(() => DeserializeName());
            return new ModuleQualifiedId(parameter0);
        }

        public ModuleQualifiedId DeserializeModuleQualifiedIdOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeModuleQualifiedId();
        }

        private ImplementationKind DeserializeImplementationKind()
        {
            int ordinal = DeserializeInt32();
            return (ImplementationKind)ordinal;
        }

        private ModuleKindEnum DeserializeModuleKindEnum()
        {
            int ordinal = DeserializeInt32();
            return (ModuleKindEnum)ordinal;
        }

        public FileModuleDefinition DeserializeFileModuleDefinition()
        {
            Microsoft.Dafny.ModuleDefinition parameter5 = null;
            var parameter0 = DeserializeSourceOrigin();
            var parameter1 = DeserializeName();
            var parameter2 = DeserializeList<IOrigin>(() => DeserializeSourceOrigin());
            var parameter3 = DeserializeModuleKindEnum();
            var parameter4 = DeserializeImplementsOption();
            var parameter6 = DeserializeAttributesOption();
            var parameter7 = DeserializeList<TopLevelDecl>(() => DeserializeAbstract<TopLevelDecl>());
            return new FileModuleDefinition(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
        }

        public FileModuleDefinition DeserializeFileModuleDefinitionOption()
        {
            if (ReadBool())
            {
                return default;
            }

            return DeserializeFileModuleDefinition();
        }

        private object DeserializeObject(System.Type actualType)
        {
            if (actualType == typeof(SourceOrigin))
            {
                return DeserializeSourceOrigin();
            }

            if (actualType == typeof(Name))
            {
                return DeserializeName();
            }

            if (actualType == typeof(ModuleDefinition))
            {
                return DeserializeModuleDefinition();
            }

            if (actualType == typeof(UserDefinedType))
            {
                return DeserializeUserDefinedType();
            }

            if (actualType == typeof(LiteralExpr))
            {
                return DeserializeLiteralExpr();
            }

            if (actualType == typeof(Attributes))
            {
                return DeserializeAttributes();
            }

            if (actualType == typeof(TypeParameter))
            {
                return DeserializeTypeParameter();
            }

            if (actualType == typeof(TypeParameterCharacteristics))
            {
                return DeserializeTypeParameterCharacteristics();
            }

            if (actualType == typeof(FrameExpression))
            {
                return DeserializeFrameExpression();
            }

            if (actualType == typeof(AttributedExpression))
            {
                return DeserializeAttributedExpression();
            }

            if (actualType == typeof(Label))
            {
                return DeserializeLabel();
            }

            if (actualType == typeof(AssertLabel))
            {
                return DeserializeAssertLabel();
            }

            if (actualType == typeof(Formal))
            {
                return DeserializeFormal();
            }

            if (actualType == typeof(Method))
            {
                return DeserializeMethod();
            }

            if (actualType == typeof(AssertStmt))
            {
                return DeserializeAssertStmt();
            }

            if (actualType == typeof(BlockStmt))
            {
                return DeserializeBlockStmt();
            }

            if (actualType == typeof(Function))
            {
                return DeserializeFunction();
            }

            if (actualType == typeof(ClassDecl))
            {
                return DeserializeClassDecl();
            }

            if (actualType == typeof(LiteralModuleDecl))
            {
                return DeserializeLiteralModuleDecl();
            }

            if (actualType == typeof(Implements))
            {
                return DeserializeImplements();
            }

            if (actualType == typeof(ModuleQualifiedId))
            {
                return DeserializeModuleQualifiedId();
            }

            if (actualType == typeof(FileModuleDefinition))
            {
                return DeserializeFileModuleDefinition();
            }

            throw new Exception();
        }
    }
}
using System;
using System.Collections.Generic;

namespace Microsoft.Dafny
{
    partial class Deserializer
    {
        public SourceOrigin DeserializeSourceOrigin()
        {
            var parameter0 = DeserializeGeneric<Token>();
            var parameter1 = DeserializeGeneric<Token>();
            var parameter2 = DeserializeGeneric<Token>();
            return new SourceOrigin(parameter0, parameter1, parameter2);
        }

        public Token DeserializeToken()
        {
            var parameter0 = DeserializeGeneric<Int32>();
            var parameter1 = DeserializeGeneric<Int32>();
            return new Token(parameter0, parameter1);
        }

        public Name DeserializeName()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<String>();
            return new Name(parameter0, parameter1);
        }

        public ModuleDefinition DeserializeModuleDefinition()
        {
            Microsoft.Dafny.ModuleDefinition parameter5 = null;
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Name>();
            var parameter2 = DeserializeList<IOrigin>();
            var parameter3 = DeserializeModuleKindEnum();
            var parameter4 = DeserializeGeneric<Implements>();
            var parameter6 = DeserializeGeneric<Attributes>();
            var parameter7 = DeserializeList<TopLevelDecl>();
            return new ModuleDefinition(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
        }

        public UserDefinedType DeserializeUserDefinedType()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Expression>();
            return new UserDefinedType(parameter0, parameter1);
        }

        public LiteralExpr DeserializeLiteralExpr()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Object>();
            return new LiteralExpr(parameter0, parameter1);
        }

        private Specification<T> DeserializeSpecification<T>()
            where T : Node
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeList<T>();
            var parameter2 = DeserializeAttributes();
            return new Specification<T>(parameter0, parameter1, parameter2);
        }

        public Attributes DeserializeAttributes()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<String>();
            var parameter2 = DeserializeList<Expression>();
            var parameter3 = DeserializeGeneric<Attributes>();
            return new Attributes(parameter0, parameter1, parameter2, parameter3);
        }

        public TypeParameter DeserializeTypeParameter()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Name>();
            var parameter2 = DeserializeGeneric<Attributes>();
            var parameter3 = DeserializeTPVarianceSyntax();
            var parameter4 = DeserializeGeneric<TypeParameterCharacteristics>();
            var parameter5 = DeserializeList<Type>();
            return new TypeParameter(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5);
        }

        public TypeParameterCharacteristics DeserializeTypeParameterCharacteristics()
        {
            return new TypeParameterCharacteristics();
        }

        private TPVarianceSyntax DeserializeTPVarianceSyntax()
        {
            int ordinal = DeserializeInt32();
            return (TPVarianceSyntax)ordinal;
        }

        public FrameExpression DeserializeFrameExpression()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Expression>();
            var parameter2 = DeserializeGeneric<String>();
            return new FrameExpression(parameter0, parameter1, parameter2);
        }

        public AttributedExpression DeserializeAttributedExpression()
        {
            var parameter0 = DeserializeGeneric<Expression>();
            var parameter1 = DeserializeGeneric<AssertLabel>();
            var parameter2 = DeserializeGeneric<Attributes>();
            return new AttributedExpression(parameter0, parameter1, parameter2);
        }

        public Label DeserializeLabel()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<String>();
            return new Label(parameter0, parameter1);
        }

        public AssertLabel DeserializeAssertLabel()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<String>();
            return new AssertLabel(parameter0, parameter1);
        }

        public Formal DeserializeFormal()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Name>();
            var parameter2 = DeserializeGeneric<Type>();
            var parameter4 = DeserializeGeneric<Boolean>();
            var parameter3 = DeserializeGeneric<Boolean>();
            var parameter5 = DeserializeGeneric<Expression>();
            var parameter6 = DeserializeGeneric<Attributes>();
            var parameter7 = DeserializeGeneric<Boolean>();
            var parameter8 = DeserializeGeneric<Boolean>();
            var parameter9 = DeserializeGeneric<Boolean>();
            var parameter10 = DeserializeGeneric<String>();
            return new Formal(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10);
        }

        public Method DeserializeMethod()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Name>();
            var parameter2 = DeserializeGeneric<Attributes>();
            var parameter3 = DeserializeGeneric<Boolean>();
            var parameter4 = DeserializeGeneric<Boolean>();
            var parameter5 = DeserializeList<TypeParameter>();
            var parameter6 = DeserializeList<Formal>();
            var parameter7 = DeserializeList<AttributedExpression>();
            var parameter8 = DeserializeList<AttributedExpression>();
            var parameter9 = DeserializeSpecification<FrameExpression>();
            var parameter10 = DeserializeSpecification<Expression>();
            var parameter11 = DeserializeList<Formal>();
            var parameter12 = DeserializeSpecification<FrameExpression>();
            var parameter13 = DeserializeGeneric<BlockStmt>();
            var parameter14 = DeserializeGeneric<SourceOrigin>();
            var parameter15 = DeserializeGeneric<Boolean>();
            return new Method(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15);
        }

        public AssertStmt DeserializeAssertStmt()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Attributes>();
            var parameter2 = DeserializeGeneric<Expression>();
            var parameter3 = DeserializeGeneric<AssertLabel>();
            return new AssertStmt(parameter0, parameter1, parameter2, parameter3);
        }

        public BlockStmt DeserializeBlockStmt()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Attributes>();
            var parameter2 = DeserializeList<Statement>();
            return new BlockStmt(parameter0, parameter1, parameter2);
        }

        public Function DeserializeFunction()
        {
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Name>();
            var parameter16 = DeserializeGeneric<Attributes>();
            var parameter2 = DeserializeGeneric<Boolean>();
            var parameter3 = DeserializeGeneric<Boolean>();
            var parameter5 = DeserializeList<TypeParameter>();
            var parameter6 = DeserializeList<Formal>();
            var parameter9 = DeserializeList<AttributedExpression>();
            var parameter11 = DeserializeList<AttributedExpression>();
            var parameter10 = DeserializeSpecification<FrameExpression>();
            var parameter12 = DeserializeSpecification<Expression>();
            var parameter4 = DeserializeGeneric<Boolean>();
            var parameter7 = DeserializeGeneric<Formal>();
            var parameter8 = DeserializeGeneric<Type>();
            var parameter13 = DeserializeGeneric<Expression>();
            var parameter14 = DeserializeGeneric<SourceOrigin>();
            var parameter15 = DeserializeGeneric<BlockStmt>();
            var parameter17 = DeserializeGeneric<SourceOrigin>();
            return new Function(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15, parameter16, parameter17);
        }

        public ClassDecl DeserializeClassDecl()
        {
            Microsoft.Dafny.ModuleDefinition parameter4 = null;
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Name>();
            var parameter2 = DeserializeGeneric<Attributes>();
            var parameter3 = DeserializeList<TypeParameter>();
            var parameter5 = DeserializeList<MemberDecl>();
            var parameter6 = DeserializeList<Type>();
            var parameter7 = DeserializeGeneric<Boolean>();
            return new ClassDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
        }

        public LiteralModuleDecl DeserializeLiteralModuleDecl()
        {
            Microsoft.Dafny.DafnyOptions parameter0 = null;
            Microsoft.Dafny.ModuleDefinition parameter4 = null;
            var parameter1 = DeserializeGeneric<SourceOrigin>();
            var parameter2 = DeserializeGeneric<Name>();
            var parameter3 = DeserializeGeneric<Attributes>();
            var parameter5 = DeserializeGeneric<String>();
            var parameter6 = DeserializeGeneric<ModuleDefinition>();
            return new LiteralModuleDecl(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6);
        }

        public Implements DeserializeImplements()
        {
            var parameter0 = DeserializeImplementationKind();
            var parameter1 = DeserializeGeneric<ModuleQualifiedId>();
            return new Implements(parameter0, parameter1);
        }

        public ModuleQualifiedId DeserializeModuleQualifiedId()
        {
            var parameter0 = DeserializeList<Name>();
            return new ModuleQualifiedId(parameter0);
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
            var parameter0 = DeserializeGeneric<SourceOrigin>();
            var parameter1 = DeserializeGeneric<Name>();
            var parameter2 = DeserializeList<IOrigin>();
            var parameter3 = DeserializeModuleKindEnum();
            var parameter4 = DeserializeGeneric<Implements>();
            var parameter6 = DeserializeGeneric<Attributes>();
            var parameter7 = DeserializeList<TopLevelDecl>();
            return new FileModuleDefinition(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7);
        }

        private object DeserializeObject(System.Type actualType)
        {
            if (actualType == typeof(SourceOrigin))
            {
                return DeserializeSourceOrigin();
            }

            if (actualType == typeof(Token))
            {
                return DeserializeToken();
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
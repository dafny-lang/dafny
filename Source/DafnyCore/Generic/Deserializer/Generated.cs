using System;
using System.Collections.Generic;

namespace Microsoft.Dafny
{
    partial class Deserializer
    {
        public SourceOrigin ReadSourceOrigin()
        {
            var parameter0 = ReadToken();
            var parameter1 = ReadTokenOption();
            var parameter2 = ReadTokenOption();
            return new SourceOrigin(parameter0, parameter1, parameter2);
        }

        public SourceOrigin ReadSourceOriginOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadSourceOrigin();
        }

        public Attributes ReadAttributes()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadString();
            var parameter2 = ReadList<Expression>(() => ReadAbstract<Expression>());
            var parameter3 = ReadAttributesOption();
            return new Attributes(parameter0, parameter1, parameter2, parameter3);
        }

        public Attributes ReadAttributesOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadAttributes();
        }

        public LiteralExpr ReadLiteralExpr()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadAbstract<Object>();
            return new LiteralExpr(parameter0, parameter1);
        }

        public LiteralExpr ReadLiteralExprOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadLiteralExpr();
        }

        public AttributedExpression ReadAttributedExpression()
        {
            var parameter0 = ReadAbstract<Expression>();
            var parameter1 = ReadAssertLabel();
            var parameter2 = ReadAttributes();
            return new AttributedExpression(parameter0, parameter1, parameter2);
        }

        public AttributedExpression ReadAttributedExpressionOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadAttributedExpression();
        }

        public Label ReadLabel()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadString();
            return new Label(parameter0, parameter1);
        }

        public Label ReadLabelOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadLabel();
        }

        public AssertLabel ReadAssertLabel()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadString();
            return new AssertLabel(parameter0, parameter1);
        }

        public AssertLabel ReadAssertLabelOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadAssertLabel();
        }

        public Name ReadName()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadString();
            return new Name(parameter0, parameter1);
        }

        public Name ReadNameOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadName();
        }

        public TypeParameter ReadTypeParameter()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadName();
            var parameter5 = ReadAttributes();
            var parameter2 = ReadTypeParameterTPVarianceSyntax();
            var parameter3 = ReadTypeParameterCharacteristics();
            var parameter4 = ReadList<Type>(() => ReadAbstract<Type>());
            return new TypeParameter(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5);
        }

        public TypeParameter ReadTypeParameterOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadTypeParameter();
        }

        public TypeParameterCharacteristics ReadTypeParameterCharacteristics()
        {
            var parameter0 = ReadTypeParameterEqualitySupportValue();
            var parameter1 = ReadTypeAutoInitInfo();
            var parameter2 = ReadBoolean();
            return new TypeParameterCharacteristics(parameter0, parameter1, parameter2);
        }

        public TypeParameterCharacteristics ReadTypeParameterCharacteristicsOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadTypeParameterCharacteristics();
        }

        private Type.AutoInitInfo ReadTypeAutoInitInfo()
        {
            int ordinal = ReadInt32();
            return (Type.AutoInitInfo)ordinal;
        }

        private TypeParameter.EqualitySupportValue ReadTypeParameterEqualitySupportValue()
        {
            int ordinal = ReadInt32();
            return (TypeParameter.EqualitySupportValue)ordinal;
        }

        private TypeParameter.TPVarianceSyntax ReadTypeParameterTPVarianceSyntax()
        {
            int ordinal = ReadInt32();
            return (TypeParameter.TPVarianceSyntax)ordinal;
        }

        public FrameExpression ReadFrameExpression()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadAbstract<Expression>();
            var parameter2 = ReadString();
            return new FrameExpression(parameter0, parameter1, parameter2);
        }

        public FrameExpression ReadFrameExpressionOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadFrameExpression();
        }

        public Formal ReadFormal()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadName();
            var parameter2 = ReadAbstract<Type>();
            var parameter4 = ReadBoolean();
            var parameter3 = ReadBoolean();
            var parameter5 = ReadAbstract<Expression>();
            var parameter6 = ReadAttributes();
            var parameter7 = ReadBoolean();
            var parameter8 = ReadBoolean();
            var parameter9 = ReadBoolean();
            var parameter10 = ReadString();
            return new Formal(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10);
        }

        public Formal ReadFormalOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadFormal();
        }

        public Method ReadMethod()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadName();
            var parameter13 = ReadAttributes();
            var parameter2 = ReadBoolean();
            var parameter3 = ReadBoolean();
            var parameter14 = ReadSourceOrigin();
            var parameter4 = ReadList<TypeParameter>(() => ReadTypeParameter());
            var parameter5 = ReadList<Formal>(() => ReadFormal());
            var parameter7 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
            var parameter10 = ReadList<AttributedExpression>(() => ReadAttributedExpression());
            var parameter8 = ReadSpecification<FrameExpression>();
            var parameter11 = ReadSpecification<Expression>();
            var parameter6 = ReadList<Formal>(() => ReadFormal());
            var parameter9 = ReadSpecification<FrameExpression>();
            var parameter12 = ReadBlockStmt();
            var parameter15 = ReadBoolean();
            return new Method(parameter0, parameter1, parameter2, parameter3, parameter4, parameter5, parameter6, parameter7, parameter8, parameter9, parameter10, parameter11, parameter12, parameter13, parameter14, parameter15);
        }

        public Method ReadMethodOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadMethod();
        }

        public AssertStmt ReadAssertStmt()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter3 = ReadAttributes();
            var parameter1 = ReadAbstract<Expression>();
            var parameter2 = ReadAssertLabel();
            return new AssertStmt(parameter0, parameter1, parameter2, parameter3);
        }

        public AssertStmt ReadAssertStmtOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadAssertStmt();
        }

        public BlockStmt ReadBlockStmt()
        {
            var parameter0 = ReadSourceOrigin();
            var parameter1 = ReadAttributes();
            var parameter2 = ReadList<Statement>(() => ReadAbstract<Statement>());
            return new BlockStmt(parameter0, parameter1, parameter2);
        }

        public BlockStmt ReadBlockStmtOption()
        {
            if (ReadIsNull())
            {
                return default;
            }

            return ReadBlockStmt();
        }

        private object ReadObject(System.Type actualType)
        {
            if (actualType == typeof(SourceOrigin))
            {
                return ReadSourceOrigin();
            }

            if (actualType == typeof(Attributes))
            {
                return ReadAttributes();
            }

            if (actualType == typeof(LiteralExpr))
            {
                return ReadLiteralExpr();
            }

            if (actualType == typeof(AttributedExpression))
            {
                return ReadAttributedExpression();
            }

            if (actualType == typeof(Label))
            {
                return ReadLabel();
            }

            if (actualType == typeof(AssertLabel))
            {
                return ReadAssertLabel();
            }

            if (actualType == typeof(Name))
            {
                return ReadName();
            }

            if (actualType == typeof(TypeParameter))
            {
                return ReadTypeParameter();
            }

            if (actualType == typeof(TypeParameterCharacteristics))
            {
                return ReadTypeParameterCharacteristics();
            }

            if (actualType == typeof(FrameExpression))
            {
                return ReadFrameExpression();
            }

            if (actualType == typeof(Formal))
            {
                return ReadFormal();
            }

            if (actualType == typeof(Method))
            {
                return ReadMethod();
            }

            if (actualType == typeof(AssertStmt))
            {
                return ReadAssertStmt();
            }

            if (actualType == typeof(BlockStmt))
            {
                return ReadBlockStmt();
            }

            throw new Exception();
        }
    }
}
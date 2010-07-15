/***************************************************************************

Copyright (c) Microsoft Corporation. All rights reserved.
This code is licensed under the Visual Studio SDK license terms.
THIS CODE IS PROVIDED *AS IS* WITHOUT WARRANTY OF
ANY KIND, EITHER EXPRESS OR IMPLIED, INCLUDING ANY
IMPLIED WARRANTIES OF FITNESS FOR A PARTICULAR
PURPOSE, MERCHANTABILITY, OR NON-INFRINGEMENT.

***************************************************************************/

using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.VisualStudio.TextManager.Interop;
using Microsoft.VisualStudio.Package;

namespace Demo
{
    public class Declarations : Microsoft.VisualStudio.Package.Declarations
    {
        IList<Declaration> declarations;
        public Declarations(IList<Declaration> declarations)
        {
            this.declarations = declarations;
        }

        public override int GetCount()
        {
            return declarations.Count;
        }

        public override string GetDescription(int index)
        {
            return declarations[index].Description;
        }

        public override string GetDisplayText(int index)
        {
            return declarations[index].DisplayText;
        }

        public override int GetGlyph(int index)
        {
            return declarations[index].Glyph;
        }

        public override string GetName(int index)
        {
            if (index >= 0)
                return declarations[index].Name;

            return null;
        }
    }
}
using System;

namespace Demo
{
    static class GuidList
    {
        public const string guidIronyLanguageServiceString = "1F9687D0-937C-428E-ACFF-A7622A14100C";
        public const string guidIronyLanguageServicePkgString = "F85E7515-4CA6-42A5-86E0-D2312AE91D23";
        public const string guidIronyLanguageServiceCmdSetString = "68251AE3-0205-4FC9-8B12-D4C3EA9F8D6C";

        public static readonly Guid guidIronyLanguageServiceCmdSet = new Guid(guidIronyLanguageServiceCmdSetString);
    };
}
using Xunit.Abstractions;
using Xunit.Sdk;

namespace DefaultNamespace {
    public class CollectionPerTestCaseTestCollectionFactory : IXunitTestCollectionFactory {
        public ITestCollection Get(ITypeInfo testClass) {
            throw new System.NotImplementedException();
        }

        public string DisplayName
        {
            get
            {
                return "collection-per-testcase";
            }
        }
    }
}
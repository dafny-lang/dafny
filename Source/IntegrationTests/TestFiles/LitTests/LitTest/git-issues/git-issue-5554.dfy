// RUN:  %dafny -compile:4 -compileTarget:cs "%s"

datatype MultisetContainer = EmptySet | BooleanMultiset(containerSet: multiset<bool>)

method Main() {
    var initialMultiset := multiset{false};
    
    for iteration := 0 to 98 {
        var multisetInstance := BooleanMultiset(initialMultiset); 
        initialMultiset := initialMultiset + multisetInstance.containerSet;  
    }
    print initialMultiset > initialMultiset;
}
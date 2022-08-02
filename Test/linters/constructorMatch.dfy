// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module WithWarning {
    datatype Color = Red | Green | ShadesOfGray(nat)
    datatype Country = Mexico | nigeria | Europe(nat) 
  
    method countryMethod (c: Country) returns (x: bool) {    
          return match c
            case nigeria => true
            case anythingElse => false;
        }
    
    method MonochromaticMethod(c: Color) returns (x: bool) {
          
          return match c
            case ShadesOfGray => true
            case anythingElse => false;
    }

    function method MonochromaticFunction(c: Color) : bool {
        match c
            case ShadesOfGray => true
            case anythingElse => false
    }
    method MonochromaticMethodloop(c: Color) returns (x: bool)  {
        var test := false;
        while test
        {
            test := match c
                case ShadesOfGray => true
                case anythingElse => false;
        }
        return false; 
    }
   

}

module WithoutWarning {
     datatype Color = Red | Green | ShadesOfGray(nat)
      datatype Country = Mexico | Nigeria | Europe(nat) 
       
      method countryMethod (c: Country) returns (x: bool) {    
          return match c
                 case Nigeria => true
                 case anythingElse => false;
          }
    
    method MonochromaticMethod(c: Color) returns (x: bool) {
          
          return match c
            case ShadesOfGray(_) => true
            case anythingElse => false;
    }

    function method MonochromaticFunction(c: Color) : bool {
        match c
            case ShadesOfGray(_) => true
            case anythingElse => false
    }
    method MonochromaticMethodloop(c: Color) returns (x: bool)  {
        while c == ShadesOfGray(3)
        {
            return true;
        }
        return false; 
    }
    method Main() {
            var x := MonochromaticMethod(Green); 
            print MonochromaticFunction(Green);
            var y := MonochromaticMethodloop(Green);
        }

}




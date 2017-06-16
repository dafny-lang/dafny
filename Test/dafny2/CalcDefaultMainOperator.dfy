// RUN: %dafny /env:0 /rprint:- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma TestBool(F: bool, T: bool)
  requires F==false && T==true
{
  calc {  // <==
    false;
    T;  // error: this step does not hold
    F;  // note: this step holds with main operator ==>
  }
  calc {  // ==>
    ((true));
    F;  // error: this step does not hold
    T;  // note: this step holds with main operator ==>
  }
  calc {  // ==>
    ((((F))));
    T;  // note: this step holds with main operator ==>
    (false);  // error: this step does not hold
  }
  calc {  // <==
    false;
    T;  // error: this step does not hold
    F;  // note: this step holds with main operator <==
  }
}

lemma TestSet(Empty: set<int>, Nonempty: set<int>)
  requires |Empty| == 0 && |Nonempty| > 0
{
  calc {  // >=
    {};
    Nonempty;  // error: this step does not hold
    Empty;  // note: this step holds with main operator >=
  }
  calc {  // <=
    Empty;
    Nonempty;  // note: this step holds with main operator <=
    ({});  // error: this step does not hold
  }
}

lemma TestMultiset(Empty: multiset<int>, Nonempty: multiset<int>)
  requires |Empty| == 0 && |Nonempty| > 0
{
  calc {  // >=
    ((((multiset{}))));
    Nonempty;  // error: this step does not hold
    Empty;  // note: this step holds with main operator >=
  }
  calc {  // <=
    Empty;
    Nonempty;  // note: this step holds with main operator <=
    multiset{};  // error: this step does not hold
  }
}

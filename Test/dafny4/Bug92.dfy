// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
module ModOpaque {
    ghost function {:opaque} Hidden(x:int) : (int, int)
    {
        (5, 7)
    }

    ghost function Visible(x:int) : (int, int)
    {
        Hidden(x)
    }

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {
        assert (y, z) == Hidden(x);
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Hidden(x);
    }
}

module ModVisible {
    ghost function Hidden(x:int) : (int, int)
    {
        (5, 7)
    }

    ghost function Visible(x:int) : (int, int)
    {
        Hidden(x)
    }

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {
        assert (y, z) == Hidden(x);
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Hidden(x);
    }
}

module ModFuel {
    ghost function {:fuel 0,0} Hidden(x:int) : (int, int)
    {
        (5, 7)
    }

    ghost function Visible(x:int) : (int, int)
    {
        Hidden(x)
    }

    lemma foo(x:int, y:int, z:int)
        requires (y, z) == Visible(x);
    {
        assert (y, z) == Hidden(x);
    }

    lemma bar(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Visible(x);
    }

    lemma baz(x:int, y:int, z:int)
        requires y == Visible(x).0;
        requires z == Visible(x).1;
    {
        assert (y, z) == Hidden(x);
    }
}
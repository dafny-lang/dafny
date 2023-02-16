// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:0 /optimizeResolution:0 /errorLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module TestModule1 {
    function pos(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos(x - 1)
    }

    method test(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert pos(z) == 0;
        assert pos(-1) == 0;
        assert pos(y) == 3 + pos(y - 3);    // error: Should fail, due to lack of fuel
        assert pos(y) == 4 + pos(y - 4);    // Succeeds, thanks to the assume from the preceding assert
    }
}

// Test with function-level fuel boost
module TestModule2 {
    function {:fuel 3} pos1(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos1(x - 1)
    }

    function {:fuel 4} pos2(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos2(x - 1)
    }

    function {:fuel 4} pos3(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos3(x - 1)
    }

    function {:opaque} {:fuel 4} pos4(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos3(x - 1)
    }

    method test(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert pos1(z) == 0;
        assert pos1(-1) == 0;
        assert pos1(y) == 3 + pos1(y - 3);
        assert pos1(y) == 4 + pos1(y - 4);

        assert pos2(z) == 0;
        assert pos2(-1) == 0;
        assert pos2(y) == 3 + pos2(y - 3);
        assert pos2(y) == 4 + pos2(y - 4);

        if (*) {
            assert pos3(y) == 5 + pos3(y - 5);  // Just enough fuel to get here
        } else {
            assert pos3(y) == 6 + pos3(y - 6);  // error: Should fail even with a boost, since boost is too small
        }

        if (*) {
            assert pos4(z) == 0;    // error: Fuel shouldn't overcome opaque
        } else {
            reveal pos4();
            assert pos4(y) == 5 + pos4(y - 5);  // With reveal, everything should work as above
        }


    }
}


module TestModule3 {
    // This fuel setting is equivalent to opaque, except for literals
    function {:fuel 0,0} pos(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos(x - 1)
    }

    method test(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert pos(z) == 0;             // error: Opaque setting hides body
        assert pos(-1) == 0;            // error: Lits also obey opaque now
        assert pos(y) == 3 + pos(y - 3);// error: Opaque setting hides body
    }
}

// Test fuel settings via different contexts
module TestModule4 {
    function pos(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos(x - 1)
    }

    // Should pass
    method {:fuel pos,3} test1(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert pos(z) == 0;
        assert pos(-1) == 0;
        assert pos(y) == 3 + pos(y - 3);
    }

    method {:fuel pos,0,0} test2(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert pos(z) == 0;               // error: Should fail due to "opaque" fuel setting
        assert pos(-1) == 0;              // error: Should fail due to "opaque" fuel setting.  Even Lits obey opaque
        assert pos(y) == 3 + pos(y - 3);  // error: Should fail due to "opaque" fuel setting
    }

    method test3(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert {:fuel pos,0,0} pos(z) == 0;               // error: fuel can't be decreased
        assert pos(-1) == 0;
        if (*) {
            assert pos(y) == 3 + pos(y - 3);  // error: Should fail without extra fuel setting
            assert pos(y) == 6 + pos(y - 6);  // error: Should fail even with previous assert turned into assume
        } else {
            assert {:fuel pos,3} pos(y) == 3 + pos(y - 3);  // Should succeed with extra fuel setting
            assert {:fuel pos,3} pos(y) == 6 + pos(y - 6);  // Should succeed thanks to previous assert turned into assume
        }
    }

    method test4(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        forall t:int {:fuel pos,3} | t > 0
            ensures true;
        {
            assert pos(y) == 3 + pos(y - 3);    // Expected to pass, due to local fuel boost
        }

        if (*) {
            calc {:fuel pos,3} {
                pos(y);
                3 + pos(y - 3);
            }
        }

        assert pos(y) == 3 + pos(y - 3);    // error: Should fail, due to lack of fuel outside the forall
    }
}

// Test fuel settings via different module contexts
module TestModule5 {
    // Test module level fuel settings, with nested modules

    module TestModule5a {
        module {:fuel TestModule5aiA.pos,3} TestModule5ai {
            module TestModule5aiA {
                function pos(x:int) : int
                {
                    if x < 0 then 0
                    else 1 + pos(x - 1)
                }

                method test(y:int, z:int)
                    requires y > 5;
                    requires z < 0;
                {
                    assert pos(z) == 0;
                    assert pos(-1) == 0;
                    assert pos(y) == 3 + pos(y - 3);    // Should pass due to intermediate module's fuel setting
                }
            }

            method test(y:int, z:int)
                requires y > 5;
                requires z < 0;
            {
                assert TestModule5aiA.pos(z) == 0;
                assert TestModule5aiA.pos(-1) == 0;
                assert TestModule5aiA.pos(y) == 3 + TestModule5aiA.pos(y - 3);    // Should pass due to module level fuel
            }
        }

        method test(y:int, z:int)
            requires y > 5;
            requires z < 0;
        {
            assert TestModule5ai.TestModule5aiA.pos(z) == 0;
            assert TestModule5ai.TestModule5aiA.pos(-1) == 0;
            assert TestModule5ai.TestModule5aiA.pos(y) == 3 + TestModule5ai.TestModule5aiA.pos(y - 3);    // error: Should fail, due to lack of fuel
        }
    }

    module {:fuel TestModule5bi.TestModule5biA.pos,3} TestModule5b {
        module  TestModule5bi {
            module TestModule5biA {
                function pos(x:int) : int
                {
                    if x < 0 then 0
                    else 1 + pos(x - 1)
                }

                method test(y:int, z:int)
                    requires y > 5;
                    requires z < 0;
                {
                    assert pos(z) == 0;
                    assert pos(-1) == 0;
                    assert pos(y) == 3 + pos(y - 3);    // Should succceed due to outer module fuel setting
                }
            }
        }
    }
}

// Test fuel setting for multiple functions
module TestModule6 {
    function pos(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos(x - 1)
    }

    function neg(x:int) : int
        decreases 1 - x;
    {
        if x > 0 then 0
        else 1 + neg(x + 1)
    }

    method test1(y:int, z:int)
        requires y > 5;
        requires z < 5;
    {
        assert pos(y) == 3 + pos(y - 3);    // error: Should fail, due to lack of fuel

        assert neg(z) == 3 + neg(z + 3);    // error: Should fail, due to lack of fuel
    }

    method {:fuel pos,3} {:fuel neg,4} test2(y:int, z:int)
        requires y > 5;
        requires z < -5;
    {
        assert pos(y) == 3 + pos(y - 3);

        assert neg(z) == 3 + neg(z + 3);
    }
}

// Test fuel settings with multiple overlapping contexts
module TestModule7 {
    function {:fuel 3} pos(x:int) : int
    {
        if x < 0 then 0
        else 1 + pos(x - 1)
    }

    function {:fuel 0,0} neg(x:int) : int
        decreases 1 - x;
    {
        if x > 0 then 0
        else 1 + neg(x + 1)
    }

    method {:fuel neg,4} {:fuel pos,0,0} test1(y:int, z:int)
        requires y > 5;
        requires z < -5;
    {
        if (*) {
            assert pos(y) == 3 + pos(y - 3);    // error: Method fuel should override function fuel, so this should fail
            assert neg(z) == 3 + neg(z + 3);    // Method fuel should override function fuel, so this succeeds
        }

        forall t:int {:fuel pos,3} | t > 0
            ensures true;
        {
            assert pos(y) == 3 + pos(y - 3);    // Statement fuel should override method fuel, so this should succeed
        }
    }
}

// Test fuel in a slightly more complicated setting
module TestModule8 {

    newtype byte = i:int | 0 <= i < 0x100
    newtype uint64 = i:int | 0 <= i < 0x10000000000000000

    datatype G = GUint64
               | GArray(elt:G)
               | GTuple(t:seq<G>)
               | GByteArray
               | GTaggedUnion(cases:seq<G>)

        datatype V = VUint64(u:uint64)
                   | VTuple(t:seq<V>)
                   | VCase(c:uint64, val:V)

        predicate {:fuel 2} ValInGrammar(val:V, grammar:G)
        {
            match val
                case VUint64(_) => grammar.GUint64?
                case VTuple(t)  => grammar.GTuple? && |t| == |grammar.t|
                                      && forall i :: 0 <= i < |t| ==> ValInGrammar(t[i], grammar.t[i])
                case VCase(c, val) => grammar.GTaggedUnion? && c as int < |grammar.cases| && ValInGrammar(val, grammar.cases[c])
        }

        datatype CRequest = CRequest(client:EndPoint, seqno:uint64, request:CAppMessage) | CRequestNoOp()

        type EndPoint
        function method EndPoint_grammar() : G { GUint64 }
        function method CRequest_grammar() : G { GTaggedUnion([ GTuple([EndPoint_grammar(), GUint64, CAppMessage_grammar()]), GUint64]) }

        function method parse_EndPoint(val:V) : EndPoint
            requires ValInGrammar(val, EndPoint_grammar());

        type CAppMessage
        function method CAppMessage_grammar() : G { GTaggedUnion([GUint64, GUint64, GUint64]) }
        function method parse_AppMessage(val:V) : CAppMessage
            requires ValInGrammar(val, CAppMessage_grammar());

        function method {:fuel ValInGrammar,1} parse_Request1(val:V) : CRequest
            requires ValInGrammar(val, CRequest_grammar());
        {
            if val.c == 0 then
                var ep := parse_EndPoint(val.val.t[0]); // With default fuel, error: function precondition (6x), destructor, index
                CRequest(ep, val.val.t[1].u, parse_AppMessage(val.val.t[2]))    // error: destructor, index
            else
                CRequestNoOp()
        }

        function method parse_Request2(val:V) : CRequest
            requires ValInGrammar(val, CRequest_grammar());
        {
            if val.c == 0 then
                var ep := parse_EndPoint(val.val.t[0]);                      // With fuel boosted to 2 this succeeds
                CRequest(ep, val.val.t[1].u, parse_AppMessage(val.val.t[2])) // error: destructor
            else
                CRequestNoOp()
        }

        function method {:fuel ValInGrammar,3} parse_Request3(val:V) : CRequest
            requires ValInGrammar(val, CRequest_grammar());
        {
            if val.c == 0 then
                var ep := parse_EndPoint(val.val.t[0]);
                CRequest(ep, val.val.t[1].u, parse_AppMessage(val.val.t[2]))    // With one more boost, everything succeeds
            else
                CRequestNoOp()
        }

        // With the method, everything succeeds with one less fuel boost (i.e., 2, rather than 3, as in parse_Request3)
        method parse_Request4(val:V) returns (req:CRequest)
            requires ValInGrammar(val, CRequest_grammar());
        {
            if val.c == 0 {
                var ep := parse_EndPoint(val.val.t[0]);
                req := CRequest(ep, val.val.t[1].u, parse_AppMessage(val.val.t[2]));
            } else {
                req := CRequestNoOp();
            }
        }
}


// Test fuel when it's applied to a non-recursive function
module TestModule9 {
    function abs(x:int) : int
    {
        if x < 0 then -1 * x else x
    }

    // All should pass.
    method test1(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert abs(z) == -1*z;
        assert abs(y) == y;
        assert abs(-1) == 1;
    }

    // Method-level fuel override
    method {:fuel abs,0,0} test2(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert abs(z) == -1*z;  // error: Cannot see the body of abs
        assert abs(y) == y;     // error: Cannot see the body of abs
        assert abs(-1) == 1;    // error: lit doesn't bypass fuel
    }

    // Statement-level fuel override
    method test3(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert {:fuel abs,0,0} abs(z) == -1*z;  // error: fuel can't be decreased
        assert abs(y) == y;     // Normal success
        assert abs(-1) == 1;    // lit bypasses fuel, so this should succeed
    }

    // Giving more fuel to a non-recursive function won't help,
    // but it shouldn't hurt either.
    method {:fuel abs,5,6} test4(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert abs(z) == -1*z;
        assert abs(y) == y;
        assert abs(-1) == 1;
    }
}

// Test fuel when it's applied to a non-recursive function directly (to simulate opaque)
module TestModule10 {
    function {:fuel 0,0} abs(x:int) : int
    {
        if x < 0 then -1 * x else x
    }

    method test1(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert abs(z) == -1*z;  // error: Cannot see the body of abs
        assert abs(y) == y;     // error: Cannot see the body of abs
        assert abs(-1) == 1;    // errro: lit does not bypass fuel
    }
}

// Test fuel when it's mentioned in other functions function to simulate a local opaque
module TestModule11 {
    function abs(x:int) : int
    {
        if x < 0 then -1 * x else x
    }

    function {:fuel abs,0,0} abs'(x:int) : int
    {
        abs(x)
    }

    method test1(y:int, z:int)
        requires y > 5;
        requires z < 0;
    {
        assert abs'(z) == -1*z;  // Annotation on abs' only applies locally, so we see the body of abs
        assert abs'(y) == y;     // Annotation on abs' only applies locally, so we see the body of abs
        assert abs'(-1) == 1;    // lit bypasses fuel, so this should succeed
    }
}

module TestModule12 {
		function pos3(x:int) : int
		{
				if x < 0 then 0
				else 1 + pos4(x - 1)
		}

		function pos4(x:int) : int
		{
				if x < 0 then 0
				else 1 + pos3(x - 1)
		}

		method {:fuel pos3,2,3} {:fuel pos4,2,3} test (y:int)
			requires y > 3;
		{
				assert pos3(y) == 3 + pos4(y - 3);
		}
}

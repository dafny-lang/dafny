// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_4(p_m_method_4_1: bool, p_m_method_4_2: bool, p_m_method_4_3: array<real>, p_m_method_4_4: bool) returns (ret_1: bool, ret_2: DT_1<int, real>, ret_3: bool, ret_4: bool)
{
	var v_DT_1_1_1: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_2: DT_1<int, real> := DT_1_1;
	var v_DT_1_1_3: DT_1<int, real> := DT_1_1;
	var v_seq_4: seq<DT_1<int, real>> := [v_DT_1_1_1, v_DT_1_1_2, v_DT_1_1_3];
	var v_int_16: int := 9;
	var v_DT_1_1_4: DT_1<int, real> := DT_1_1;
	var v_seq_5: seq<int> := [12];
	var v_bool_5: bool := m_method_3(v_seq_5);
	var v_seq_6: seq<int> := [];
	var v_bool_6: bool := m_method_3(v_seq_6);
	return p_m_method_4_1, (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_16]) else (v_DT_1_1_4)), v_bool_5, v_bool_6;
}

method m_method_3(p_m_method_3_1: seq<int>) returns (ret_1: bool)
	requires (|p_m_method_3_1| == 2 && (p_m_method_3_1[0] == 10) && (p_m_method_3_1[1] == 14));
	ensures ((|p_m_method_3_1| == 2 && (p_m_method_3_1[0] == 10) && (p_m_method_3_1[1] == 14)) ==> ((ret_1 == false)));
{
	print "p_m_method_3_1", " ", p_m_method_3_1, "\n";
	return false;
}

method safe_division(p_safe_division_1: int, p_safe_division_2: int) returns (ret_1: int)
	ensures (p_safe_division_2 == 0 ==> ret_1 == p_safe_division_1) && (p_safe_division_2 != 0 ==> ret_1 == p_safe_division_1 / p_safe_division_2);
{
	return (if ((p_safe_division_2 != 0)) then ((p_safe_division_1 / p_safe_division_2)) else (p_safe_division_1));
}

method safe_subsequence(p_safe_subsequence_1: seq, p_safe_subsequence_2: int, p_safe_subsequence_3: int) returns (ret_1: int, ret_2: int)
	ensures ((|p_safe_subsequence_1| > 0) ==> ((0 <= ret_1 < |p_safe_subsequence_1|) && (0 <= ret_2 < |p_safe_subsequence_1|) && ret_1 <= ret_2)) && ((((0 <= p_safe_subsequence_2 < |p_safe_subsequence_1|) ==> (ret_1 == p_safe_subsequence_2)) && ((0 > p_safe_subsequence_2 || p_safe_subsequence_2 >= |p_safe_subsequence_1|) ==> (ret_1 == 0)) && ((0 <= p_safe_subsequence_3 < |p_safe_subsequence_1|) ==> (ret_2 == p_safe_subsequence_3)) && ((0 > p_safe_subsequence_3 || p_safe_subsequence_3 >= |p_safe_subsequence_1|) ==> (ret_2 == 0))) || ((((0 <= p_safe_subsequence_2 < |p_safe_subsequence_1|) ==> (ret_2 == p_safe_subsequence_2)) && ((0 > p_safe_subsequence_2 || p_safe_subsequence_2 >= |p_safe_subsequence_1|) ==> (ret_2 == 0)) && ((0 <= p_safe_subsequence_3 < |p_safe_subsequence_1|) ==> (ret_1 == p_safe_subsequence_3)) && ((0 > p_safe_subsequence_3 || p_safe_subsequence_3 >= |p_safe_subsequence_1|) ==> (ret_1 == 0)))));
{
	var v_seq_1: seq := p_safe_subsequence_1;
	var v_int_2: int := p_safe_subsequence_2;
	var v_int_3: int := safe_index_seq(v_seq_1, v_int_2);
	var v_int_1: int := v_int_3;
	var v_seq_2: seq := p_safe_subsequence_1;
	var v_int_5: int := p_safe_subsequence_3;
	var v_int_6: int := safe_index_seq(v_seq_2, v_int_5);
	var v_int_4: int := v_int_6;
	if (v_int_1 <= v_int_4) {
		return v_int_1, v_int_4;
	} else {
		return v_int_4, v_int_1;
	}
}

method m_method_2(p_m_method_2_1: seq<bool>, p_m_method_2_2: array<bool>, p_m_method_2_3: char, p_m_method_2_4: int) returns (ret_1: int)
	requires (p_m_method_2_2.Length == 5 && (p_m_method_2_2[0] == true) && (p_m_method_2_2[1] == false) && (p_m_method_2_2[2] == true) && (p_m_method_2_2[3] == true) && (p_m_method_2_2[4] == false) && |p_m_method_2_1| == 0 && (p_m_method_2_4 == 289) && (p_m_method_2_3 == 'a'));
	ensures ((p_m_method_2_2.Length == 5 && (p_m_method_2_2[0] == true) && (p_m_method_2_2[1] == false) && (p_m_method_2_2[2] == true) && (p_m_method_2_2[3] == true) && (p_m_method_2_2[4] == false) && |p_m_method_2_1| == 0 && (p_m_method_2_4 == 289) && (p_m_method_2_3 == 'a')) ==> ((ret_1 == -352)));
	modifies p_m_method_2_2;
{
	var v_char_int_int_1: (char, int, int) := ('z', 20, -6);
	var v_char_int_int_2: (char, int, int) := ('U', 13, 23);
	var v_bool_1: bool, v_char_int_int_3: (char, int, int), v_bool_2: bool, v_bool_3: bool := p_m_method_2_2[2], (if (true) then (v_char_int_int_1) else (v_char_int_int_2)), (if (true) then (false) else (false)), ('C' !in map['I' := -3.91, 'u' := -5.01]);
	var v_int_11: int, v_int_12: int := (match 'B' {
		case 'O' => 20
		case 'w' => 25
		case _ => 9
	}), v_char_int_int_1.1;
	for v_int_10 := v_int_11 to v_int_12 
		invariant (v_int_12 - v_int_10 >= 0)
	{
		if p_m_method_2_2[1] {
			return p_m_method_2_4;
		}
		var v_char_int_int_4: (char, int, int) := ('U', 13, 23);
		var v_char_int_int_5: (char, int, int) := ('z', 20, -6);
		assert ((v_char_int_int_2 == v_char_int_int_4) && (p_m_method_2_3 == 'a') && (v_char_int_int_1.2 == -6) && (v_char_int_int_3 == v_char_int_int_5) && (p_m_method_2_2[0] == true));
		expect ((v_char_int_int_2 == v_char_int_int_4) && (p_m_method_2_3 == 'a') && (v_char_int_int_1.2 == -6) && (v_char_int_int_3 == v_char_int_int_5) && (p_m_method_2_2[0] == true));
		var v_char_int_int_6: (char, int, int) := ('z', 20, -6);
		var v_char_int_int_7: (char, int, int) := ('z', 20, -6);
		var v_char_int_int_8: (char, int, int) := ('U', 13, 23);
		print "v_int_10", " ", v_int_10, " ", "v_bool_1", " ", v_bool_1, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "p_m_method_2_2[2]", " ", p_m_method_2_2[2], " ", "p_m_method_2_2[1]", " ", p_m_method_2_2[1], " ", "v_char_int_int_1.0", " ", (v_char_int_int_1.0 == 'z'), " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_char_int_int_2.2", " ", v_char_int_int_2.2, " ", "v_char_int_int_1.1", " ", v_char_int_int_1.1, " ", "v_char_int_int_2.0", " ", (v_char_int_int_2.0 == 'U'), " ", "v_char_int_int_1.2", " ", v_char_int_int_1.2, " ", "v_char_int_int_2.1", " ", v_char_int_int_2.1, " ", "p_m_method_2_2[0]", " ", p_m_method_2_2[0], " ", "p_m_method_2_3", " ", (p_m_method_2_3 == 'a'), " ", "v_char_int_int_1", " ", (v_char_int_int_1 == v_char_int_int_6), " ", "p_m_method_2_2", " ", "v_char_int_int_3", " ", (v_char_int_int_3 == v_char_int_int_7), " ", "p_m_method_2_4", " ", p_m_method_2_4, " ", "v_char_int_int_2", " ", (v_char_int_int_2 == v_char_int_int_8), "\n";
	}
	var v_seq_3: seq<int> := [10, 14];
	var v_bool_4: bool := m_method_3(v_seq_3);
	if v_bool_4 {
		var v_int_14: int, v_int_15: int := p_m_method_2_4, v_int_11;
		for v_int_13 := v_int_14 to v_int_15 
			invariant (v_int_15 - v_int_13 >= 0)
		{
			return 16;
		}
		var v_bool_8: bool := v_bool_2;
		var v_bool_9: bool := (true <==> true);
		var v_array_1: array<real> := new real[3];
		v_array_1[0] := -6.62;
		v_array_1[1] := 18.35;
		v_array_1[2] := -23.00;
		var v_array_2: array<real> := new real[4];
		v_array_2[0] := 1.07;
		v_array_2[1] := -15.54;
		v_array_2[2] := 5.12;
		v_array_2[3] := -29.55;
		var v_array_3: array<real> := new real[3] [11.91, 8.92, -28.89];
		var v_array_4: array<real> := new real[4] [-0.24, -5.61, 2.97, 5.15];
		var v_map_1: map<bool, array<real>> := map[false := v_array_1, true := v_array_2, false := v_array_3, false := v_array_4];
		var v_bool_7: bool := true;
		var v_array_5: array<real> := new real[5] [19.02, -14.21, -21.73, 9.75, 29.28];
		var v_array_6: array<real> := (if ((v_bool_7 in v_map_1)) then (v_map_1[v_bool_7]) else (v_array_5));
		var v_bool_10: bool := (2 >= 28);
		var v_bool_11: bool, v_DT_1_1_5: DT_1<int, real>, v_bool_12: bool, v_bool_13: bool := m_method_4(v_bool_8, v_bool_9, v_array_6, v_bool_10);
		p_m_method_2_2[0], v_DT_1_1_5, v_bool_2, v_bool_9 := v_bool_11, v_DT_1_1_5, v_bool_12, v_bool_13;
		assert true;
		expect true;
		assert true;
		expect true;
		assert true;
		expect true;
	} else {
		var v_map_2: map<bool, int> := map[true := 20];
		var v_bool_14: bool := false;
		var v_int_18: int, v_int_19: int := (if ((v_bool_14 in v_map_2)) then (v_map_2[v_bool_14]) else (17)), (7 / 19);
		for v_int_17 := v_int_18 downto v_int_19 
			invariant (v_int_17 - v_int_19 >= 0)
		{
			var v_char_int_int_29: (char, int, int) := ('z', 20, -6);
			var v_char_int_int_30: (char, int, int) := ('z', 20, -6);
			var v_char_int_int_31: (char, int, int) := ('U', 13, 23);
			print "v_int_17", " ", v_int_17, " ", "v_bool_14", " ", v_bool_14, " ", "v_map_2", " ", (v_map_2 == map[true := 20]), " ", "v_bool_1", " ", v_bool_1, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "p_m_method_2_2[2]", " ", p_m_method_2_2[2], " ", "p_m_method_2_2[1]", " ", p_m_method_2_2[1], " ", "v_bool_4", " ", v_bool_4, " ", "v_char_int_int_1.0", " ", (v_char_int_int_1.0 == 'z'), " ", "v_int_12", " ", v_int_12, " ", "p_m_method_2_1", " ", p_m_method_2_1, " ", "v_int_11", " ", v_int_11, " ", "v_char_int_int_2.2", " ", v_char_int_int_2.2, " ", "v_seq_3", " ", v_seq_3, " ", "v_char_int_int_1.1", " ", v_char_int_int_1.1, " ", "v_char_int_int_2.0", " ", (v_char_int_int_2.0 == 'U'), " ", "v_char_int_int_1.2", " ", v_char_int_int_1.2, " ", "v_char_int_int_2.1", " ", v_char_int_int_2.1, " ", "p_m_method_2_2[0]", " ", p_m_method_2_2[0], " ", "p_m_method_2_3", " ", (p_m_method_2_3 == 'a'), " ", "v_char_int_int_1", " ", (v_char_int_int_1 == v_char_int_int_29), " ", "p_m_method_2_2", " ", "v_char_int_int_3", " ", (v_char_int_int_3 == v_char_int_int_30), " ", "p_m_method_2_4", " ", p_m_method_2_4, " ", "v_char_int_int_2", " ", (v_char_int_int_2 == v_char_int_int_31), "\n";
			return (16 * -22);
		}
		var v_seq_7: seq<int> := [10];
		var v_bool_15: bool := m_method_3(v_seq_7);
		v_bool_2, v_bool_3, v_bool_14, v_bool_1, p_m_method_2_2[2] := p_m_method_2_2[2], v_bool_15, (false in map[true := false, true := false, true := false, false := false, false := true]), p_m_method_2_2[0], v_bool_4;
		var v_seq_8: seq<int> := [5];
		var v_bool_16: bool := m_method_3(v_seq_8);
		v_bool_4, p_m_method_2_2[0], v_bool_3, v_bool_15 := v_bool_3, v_bool_16, ('E' != 'q'), v_bool_3;
		p_m_method_2_2[2], v_bool_16 := (if (false) then (false) else (true)), v_bool_3;
		var v_map_3: map<bool, bool> := map[false := false];
		var v_bool_17: bool := false;
		if (if ((v_bool_17 in v_map_3)) then (v_map_3[v_bool_17]) else (false)) {
			return (4 / -14);
		} else {
			return v_char_int_int_2.2;
		}
	}
	var v_bool_18: bool, v_real_1: real, v_bool_19: bool, v_bool_20: bool := (false && false), (if (true) then (23.72) else (29.19)), (multiset({false, true}) > multiset{false, false, false, true}), (match false {
		case _ => true
	});
	var v_map_4: map<bool, int> := map[true := 10];
	var v_bool_21: bool := true;
	var v_int_20: int := (if ((v_bool_21 in v_map_4)) then (v_map_4[v_bool_21]) else (18));
	var v_int_21: int := (match false {
		case _ => 29
	});
	while (v_int_20 < v_int_21) 
		decreases v_int_21 - v_int_20;
		invariant (v_int_20 <= v_int_21);
	{
		v_int_20 := (v_int_20 + 1);
	}
	match (true <==> true) {
		case _ => {
			if (if (false) then (true) else (false)) {
				var v_map_7: map<char, int> := map['u' := 2, 'e' := 7, 'u' := 17, 'c' := 13, 'H' := 21];
				var v_char_2: char := 's';
				return (if ((v_char_2 in v_map_7)) then (v_map_7[v_char_2]) else (27));
			} else {
				
			}
			assert true;
			expect true;
		}
		
	}
	
	return (if (false) then (11) else (6));
}

method m_method_1(p_m_method_1_1: (real, bool, bool)) returns (ret_1: int)
	requires ((-16.65 < (p_m_method_1_1).0 < -16.45) && ((p_m_method_1_1).1 == true) && ((p_m_method_1_1).2 == false)) || ((17.57 < (p_m_method_1_1).0 < 17.77) && ((p_m_method_1_1).1 == true) && ((p_m_method_1_1).2 == false));
	ensures (((17.57 < (p_m_method_1_1).0 < 17.77) && ((p_m_method_1_1).1 == true) && ((p_m_method_1_1).2 == false)) ==> ((ret_1 == 27))) && (((-16.65 < (p_m_method_1_1).0 < -16.45) && ((p_m_method_1_1).1 == true) && ((p_m_method_1_1).2 == false)) ==> ((ret_1 == 27)));
{
	var v_seq_12: seq<bool> := [];
	var v_seq_13: seq<bool> := v_seq_12;
	var v_int_32: int := 29;
	var v_int_33: int := safe_index_seq(v_seq_13, v_int_32);
	var v_int_34: int := v_int_33;
	var v_seq_15: seq<bool> := (if ((|v_seq_12| > 0)) then (v_seq_12[v_int_34 := true]) else (v_seq_12));
	var v_array_7: array<bool> := new bool[5] [true, false, true, true, false];
	var v_array_8: array<bool> := new bool[5] [false, false, true, true, true];
	var v_array_9: array<bool> := new bool[5] [false, true, true, false, false];
	var v_map_8: map<bool, array<bool>> := map[false := v_array_7, true := v_array_8];
	var v_bool_25: bool := false;
	var v_array_10: array<bool> := new bool[4];
	v_array_10[0] := true;
	v_array_10[1] := true;
	v_array_10[2] := false;
	v_array_10[3] := false;
	var v_array_11: array<bool> := (if ((v_bool_25 in v_map_8)) then (v_map_8[v_bool_25]) else (v_array_10));
	var v_seq_14: seq<char> := ['a', 'v', 'E'];
	var v_int_35: int := 9;
	var v_seq_66: seq<char> := v_seq_14;
	var v_int_116: int := v_int_35;
	var v_int_117: int := safe_index_seq(v_seq_66, v_int_116);
	v_int_35 := v_int_117;
	var v_char_3: char := (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_35]) else ('c'));
	var v_int_36: int := (17 * 17);
	var v_int_37: int := m_method_2(v_seq_15, v_array_11, v_char_3, v_int_36);
	var v_int_38: int := 0;
	var v_int_39: int := -13;
	var v_int_40: int := safe_modulus(v_int_38, v_int_39);
	var v_array_12: array<(int, bool)> := new (int, bool)[4];
	var v_int_bool_1: (int, bool) := (18, true);
	v_array_12[0] := v_int_bool_1;
	var v_int_bool_2: (int, bool) := (25, true);
	v_array_12[1] := v_int_bool_2;
	var v_int_bool_3: (int, bool) := (19, false);
	v_array_12[2] := v_int_bool_3;
	var v_int_bool_4: (int, bool) := (7, true);
	v_array_12[3] := v_int_bool_4;
	var v_int_47: int, v_int_48: int := v_int_37, (match false {
		case false => v_int_40
		case true => v_array_12.Length
		case _ => (match false {
			case _ => 26
		})
	});
	for v_int_9 := v_int_47 to v_int_48 
		invariant (v_int_48 - v_int_9 >= 0) && ((((v_int_9 == -310)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -334)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -225)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -104)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -322)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -237)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -116)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -201)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -346)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -213)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -31)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -249)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -128)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -55)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -43)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -79)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -67)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -184)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -196)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -281)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -160)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -293)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -172)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -200)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -321)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -345)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -236)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -115)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -333)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -248)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -127)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -212)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -224)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -103)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -20)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -139)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -44)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -32)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -68)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -56)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -280)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -195)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -292)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -171)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -183)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -211)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -332)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -320)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -247)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -126)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -344)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -259)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -138)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -223)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -102)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -235)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -114)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -53)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -41)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -77)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -65)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -89)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -291)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -170)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -182)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -194)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -210)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -222)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -101)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -343)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -331)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -258)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -137)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -149)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -234)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -113)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -246)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -125)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -42)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -30)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -66)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -54)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -78)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -290)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -181)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -193)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -188)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -285)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -164)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -91)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -297)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -176)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -314)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -302)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -338)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -229)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -108)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -326)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -205)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -11)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -217)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -35)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -23)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -59)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -47)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -261)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -140)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -273)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -152)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -199)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -296)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -175)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -80)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -187)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -301)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -204)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -92)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -325)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -313)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -349)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -119)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -337)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -216)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -228)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -107)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -24)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -12)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -48)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -36)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -1)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -272)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -151)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -284)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -163)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -260)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -186)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -198)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -312)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -203)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -300)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -215)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -336)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -324)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -348)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -227)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -106)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -33)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -239)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -118)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -21)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -57)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -45)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -69)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -283)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -162)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -295)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -174)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -271)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -150)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -197)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -90)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -323)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -214)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -311)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -226)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -105)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -347)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -335)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -202)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -238)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -117)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -22)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -129)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -10)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -46)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -34)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -58)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -294)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -173)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -185)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -270)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -282)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -161)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -265)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -144)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -277)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -156)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -241)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -120)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -253)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -132)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -71)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -289)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -168)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -95)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -83)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -318)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -306)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -209)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -15)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -39)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -27)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -4)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -350)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -276)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -155)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -288)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -167)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -252)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -131)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -264)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -143)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -60)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -179)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -84)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -72)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -305)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -208)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -96)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -329)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -317)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -28)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -16)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -5)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -240)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -287)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -166)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -299)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -178)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -263)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -142)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -275)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -154)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -93)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -81)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -316)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -207)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -304)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -219)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -328)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -13)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -37)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -25)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -49)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -2)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -251)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -130)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -298)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -177)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -189)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -274)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -153)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -286)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -165)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -82)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -70)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -303)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -94)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -327)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -218)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -315)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -109)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -339)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -206)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -26)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -14)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -38)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -3)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -250)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -262)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -141)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -330)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -221)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -100)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -233)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -112)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -342)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -269)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -148)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -245)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -124)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -51)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -257)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -136)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -75)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -63)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -99)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -87)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -19)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -180)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -192)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -8)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -341)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -232)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -111)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -244)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -123)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -220)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -159)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -256)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -135)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -40)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -268)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -147)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -64)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -52)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -88)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -76)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -309)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -191)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -9)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -352)) ==> ((((v_int_34 == 0))))) && (((v_int_9 == -243)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -122)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -340)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -255)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -134)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -231)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -110)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -267)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -146)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -73)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -279)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -158)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -61)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -97)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -85)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -308)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -17)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -29)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -6)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -190)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -254)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -133)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -351)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -266)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -145)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -230)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -242)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -121)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -278)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -157)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -62)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -169)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -50)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -86)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -74)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -307)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -98)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -319)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -18)) ==> ((((v_int_34 == 10))))) && (((v_int_9 == -7)) ==> ((((v_int_34 == 10))))))
	{
		var v_map_10: map<int, int> := (match 15 {
			case 23 => map[20 := 29]
			case _ => map[5 := 16, 27 := 17, 18 := 9, 2 := -9]
		});
		var v_map_9: map<int, int> := map[9 := 19, 25 := 4];
		var v_int_41: int := 25;
		var v_int_43: int := (if ((v_int_41 in v_map_9)) then (v_map_9[v_int_41]) else (13));
		var v_seq_16: seq<int> := [10, 0, 18];
		var v_int_42: int := 4;
		var v_seq_67: seq<int> := v_seq_16;
		var v_int_118: int := v_int_42;
		var v_int_119: int := safe_index_seq(v_seq_67, v_int_118);
		v_int_42 := v_int_119;
		var v_map_11: map<int, int> := v_map_10;
		var v_int_44: int := (13 * 4);
		var v_int_int_int_1: (int, int, int) := (5, 3, 27);
		var v_int_int_int_2: (int, int, int) := (24, 11, 3);
		var v_int_int_int_3: (int, int, int) := (0, 23, -2);
		var v_int_int_int_4: (int, int, int) := (12, 6, 5);
		var v_int_int_int_5: (int, int, int) := (5, -22, 18);
		var v_map_12: map<(int, int, int), seq<int>> := map[v_int_int_int_1 := [], v_int_int_int_2 := [], v_int_int_int_3 := [5, -22], v_int_int_int_4 := [], v_int_int_int_5 := [29, 16, -19, 25]];
		var v_int_int_int_6: (int, int, int) := (9, -24, 24);
		var v_int_int_int_7: (int, int, int) := v_int_int_int_6;
		var v_seq_17: seq<int> := (if ((v_int_int_int_7 in v_map_12)) then (v_map_12[v_int_int_int_7]) else ([8]));
		var v_int_45: int := (if (true) then (21) else (1));
		var v_seq_68: seq<int> := v_seq_17;
		var v_int_120: int := v_int_45;
		var v_int_121: int := safe_index_seq(v_seq_68, v_int_120);
		v_int_45 := v_int_121;
		var v_array_13: array<int> := new int[3] [16, 2, 5];
		var v_array_14: array<int> := new int[5];
		v_array_14[0] := 6;
		v_array_14[1] := 25;
		v_array_14[2] := 17;
		v_array_14[3] := 28;
		v_array_14[4] := 2;
		var v_seq_18: seq<array<int>> := [v_array_13, v_array_14];
		var v_int_46: int := 24;
		var v_seq_69: seq<array<int>> := v_seq_18;
		var v_int_122: int := v_int_46;
		var v_int_123: int := safe_index_seq(v_seq_69, v_int_122);
		v_int_46 := v_int_123;
		var v_array_15: array<int> := new int[4];
		v_array_15[0] := 15;
		v_array_15[1] := 0;
		v_array_15[2] := 14;
		v_array_15[3] := 3;
		v_array_14[4], v_int_34, v_array_13[2], v_int_44, v_int_43 := v_int_37, (if ((v_int_43 in v_map_10)) then (v_map_10[v_int_43]) else ((if ((|v_seq_16| > 0)) then (v_seq_16[v_int_42]) else (9)))), (if ((v_int_44 in v_map_11)) then (v_map_11[v_int_44]) else (v_int_35)), (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_45]) else (|[19, 21]|)), (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_46]) else (v_array_15)).Length;
		var v_int_int_int_8: (int, int, int) := (0, 23, -2);
		var v_int_int_int_9: (int, int, int) := (12, 6, 5);
		var v_int_int_int_10: (int, int, int) := (5, 3, 27);
		var v_int_int_int_11: (int, int, int) := (5, -22, 18);
		var v_int_int_int_12: (int, int, int) := (24, 11, 3);
		var v_real_bool_bool_7: (real, bool, bool) := (17.67, true, false);
		print "v_array_15[2]", " ", v_array_15[2], " ", "v_array_13[0]", " ", v_array_13[0], " ", "v_array_14[1]", " ", v_array_14[1], " ", "v_map_11", " ", (v_map_11 == map[18 := 9, 2 := -9, 5 := 16, 27 := 17]), " ", "v_map_12", " ", (v_map_12 == map[v_int_int_int_8 := [5, -22], v_int_int_int_9 := [], v_int_int_int_10 := [], v_int_int_int_11 := [29, 16, -19, 25], v_int_int_int_12 := []]), " ", "v_map_10", " ", (v_map_10 == map[18 := 9, 2 := -9, 5 := 16, 27 := 17]), " ", "v_int_46", " ", v_int_46, " ", "v_int_45", " ", v_int_45, " ", "v_int_44", " ", v_int_44, " ", "v_int_43", " ", v_int_43, " ", "v_int_int_int_2.1", " ", v_int_int_int_2.1, " ", "v_int_int_int_3", " ", v_int_int_int_3, " ", "v_int_int_int_2.2", " ", v_int_int_int_2.2, " ", "v_int_int_int_4", " ", v_int_int_int_4, " ", "v_int_int_int_4.0", " ", v_int_int_int_4.0, " ", "v_int_int_int_1", " ", v_int_int_int_1, " ", "v_int_int_int_4.1", " ", v_int_int_int_4.1, " ", "v_int_int_int_2", " ", v_int_int_int_2, " ", "v_int_int_int_4.2", " ", v_int_int_int_4.2, " ", "v_int_int_int_6.0", " ", v_int_int_int_6.0, " ", "v_int_42", " ", v_int_42, " ", "v_int_int_int_7", " ", v_int_int_int_7, " ", "v_int_41", " ", v_int_41, " ", "v_int_int_int_5", " ", v_int_int_int_5, " ", "v_int_int_int_2.0", " ", v_int_int_int_2.0, " ", "v_int_int_int_6", " ", v_int_int_int_6, " ", "v_array_14[4]", " ", v_array_14[4], " ", "v_int_int_int_5.2", " ", v_int_int_int_5.2, " ", "v_array_14[0]", " ", v_array_14[0], " ", "v_array_15[1]", " ", v_array_15[1], " ", "v_int_34", " ", v_int_34, " ", "v_array_14[3]", " ", v_array_14[3], " ", "v_array_15[0]", " ", v_array_15[0], " ", "v_array_13[2]", " ", v_array_13[2], " ", "v_seq_18", " ", (v_seq_18 == [v_array_13, v_array_14]), " ", "v_seq_16", " ", v_seq_16, " ", "v_seq_17", " ", v_seq_17, " ", "v_int_9", " ", v_int_9, " ", "v_int_int_int_1.2", " ", v_int_int_int_1.2, " ", "v_int_int_int_3.0", " ", v_int_int_int_3.0, " ", "v_int_int_int_3.1", " ", v_int_int_int_3.1, " ", "v_int_int_int_3.2", " ", v_int_int_int_3.2, " ", "v_int_int_int_5.0", " ", v_int_int_int_5.0, " ", "v_int_int_int_5.1", " ", v_int_int_int_5.1, " ", "v_array_15", " ", (v_array_15 == v_array_15), " ", "v_array_14", " ", (v_array_14 == v_array_14), " ", "v_int_int_int_1.0", " ", v_int_int_int_1.0, " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "v_int_int_int_1.1", " ", v_int_int_int_1.1, " ", "v_array_15[3]", " ", v_array_15[3], " ", "v_map_9", " ", (v_map_9 == map[9 := 19, 25 := 4]), " ", "v_int_int_int_6.1", " ", v_int_int_int_6.1, " ", "v_array_13[1]", " ", v_array_13[1], " ", "v_int_int_int_6.2", " ", v_int_int_int_6.2, " ", "v_array_14[2]", " ", v_array_14[2], " ", "p_m_method_1_1.2", " ", p_m_method_1_1.2, " ", "v_array_7[1]", " ", v_array_7[1], " ", "v_array_11", " ", (v_array_11 == v_array_7), " ", "v_array_10", " ", (v_array_10 == v_array_10), " ", "p_m_method_1_1.0", " ", (p_m_method_1_1.0 == 17.67), " ", "v_array_7[3]", " ", v_array_7[3], " ", "p_m_method_1_1.1", " ", p_m_method_1_1.1, " ", "v_array_10[3]", " ", v_array_10[3], " ", "v_array_10[1]", " ", v_array_10[1], " ", "v_seq_14", " ", (v_seq_14 == ['a', 'v', 'E']), " ", "v_seq_15", " ", v_seq_15, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == v_real_bool_bool_7), " ", "v_seq_12", " ", v_seq_12, " ", "v_seq_13", " ", v_seq_13, " ", "v_bool_25", " ", v_bool_25, " ", "v_array_9[4]", " ", v_array_9[4], " ", "v_array_7", " ", (v_array_7 == v_array_7), " ", "v_array_8[3]", " ", v_array_8[3], " ", "v_array_9[2]", " ", v_array_9[2], " ", "v_array_8", " ", (v_array_8 == v_array_8), " ", "v_array_8[1]", " ", v_array_8[1], " ", "v_array_9", " ", (v_array_9 == v_array_9), " ", "v_array_9[0]", " ", v_array_9[0], " ", "v_array_7[0]", " ", v_array_7[0], " ", "v_array_7[2]", " ", v_array_7[2], " ", "v_char_3", " ", (v_char_3 == 'a'), " ", "v_array_7[4]", " ", v_array_7[4], " ", "v_map_8", " ", (v_map_8 == map[false := v_array_7, true := v_array_8]), " ", "v_array_10[2]", " ", v_array_10[2], " ", "v_array_10[0]", " ", v_array_10[0], " ", "v_int_35", " ", v_int_35, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_32", " ", v_int_32, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_array_8[4]", " ", v_array_8[4], " ", "v_array_9[3]", " ", v_array_9[3], " ", "v_array_8[2]", " ", v_array_8[2], " ", "v_array_9[1]", " ", v_array_9[1], " ", "v_array_8[0]", " ", v_array_8[0], "\n";
		continue;
	}
	var v_seq_19: seq<int> := ([27, 12, 9] + [24, 7, 3]);
	var v_int_49: int := (if (true) then (17) else (15));
	var v_seq_70: seq<int> := v_seq_19;
	var v_int_124: int := v_int_49;
	var v_int_125: int := safe_index_seq(v_seq_70, v_int_124);
	v_int_49 := v_int_125;
	var v_seq_20: seq<int> := [24, 16];
	var v_int_50: int := 8;
	var v_seq_71: seq<int> := v_seq_20;
	var v_int_126: int := v_int_50;
	var v_int_127: int := safe_index_seq(v_seq_71, v_int_126);
	v_int_50 := v_int_127;
	v_int_49, v_int_34, v_int_35, v_int_37 := (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_49]) else ((if (false) then (21) else (26)))), v_int_36, (match 14 {
		case 19 => v_int_35
		case -26 => (match 9 {
			case _ => 15
		})
		case _ => (if ((|v_seq_20| > 0)) then (v_seq_20[v_int_50]) else (22))
	}), ((-0.49).Floor * (12 - 11));
	assert ((v_array_10[0] == true) && (v_int_32 == 29) && (v_array_9[1] == true));
	expect ((v_array_10[0] == true) && (v_int_32 == 29) && (v_array_9[1] == true));
	assert ((v_array_8[2] == true) && (v_array_9[1] == true) && (v_array_7[1] == false));
	expect ((v_array_8[2] == true) && (v_array_9[1] == true) && (v_array_7[1] == false));
	var v_seq_21: seq<int> := [28, 25, 19, 4];
	var v_seq_72: seq<int> := v_seq_21;
	var v_int_130: int := 10;
	var v_int_131: int := 0;
	var v_int_132: int, v_int_133: int := safe_subsequence(v_seq_72, v_int_130, v_int_131);
	var v_int_128: int, v_int_129: int := v_int_132, v_int_133;
	var v_seq_23: seq<int> := (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_128..v_int_129]) else (v_seq_21));
	var v_seq_22: seq<int> := [20, 28];
	var v_int_52: int := 26;
	var v_seq_73: seq<int> := v_seq_22;
	var v_int_134: int := v_int_52;
	var v_int_135: int := safe_index_seq(v_seq_73, v_int_134);
	v_int_52 := v_int_135;
	var v_int_53: int := (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_52]) else (4));
	var v_map_13: map<int, int> := map[11 := 15, 12 := 29, 8 := 28];
	var v_int_54: int := -22;
	var v_int_61: int, v_int_62: int := (if ((|v_seq_23| > 0)) then (v_seq_23[v_int_53]) else ((if ((v_int_54 in v_map_13)) then (v_map_13[v_int_54]) else (20)))), v_int_34;
	for v_int_51 := v_int_61 to v_int_62 
		invariant (v_int_62 - v_int_51 >= 0) && ((((v_int_51 == 20)) ==> ((((v_int_36 == 289)) && ((v_int_34 == 289)) && (|v_seq_23| == 0) && ((v_int_37 == -1)) && ((v_int_52 == 0))))))
	{
		var v_seq_24: seq<int> := [];
		var v_seq_25: seq<int> := v_seq_24;
		var v_int_55: int := 3;
		var v_int_56: int := safe_index_seq(v_seq_25, v_int_55);
		var v_int_57: int := v_int_56;
		var v_seq_26: seq<int> := ([17] + []);
		var v_int_58: int := v_int_52;
		v_seq_23, v_int_37, v_int_52, v_int_36, v_int_34 := (if (v_array_7[1]) then ((if ((|v_seq_24| > 0)) then (v_seq_24[v_int_57 := 2]) else (v_seq_24))) else ((if (false) then ([1, 26, 17]) else ([-14])))), (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_58]) else (v_int_49)), v_int_48, ((match 27 {
			case 3 => 22
			case 6 => 3
			case _ => 13
		}) - v_int_48), v_int_36;
		if (if (v_array_7[3]) then (v_array_7[4]) else ((13.20 > 11.92))) {
			
		} else {
			var v_map_15: map<int, bool> := map[14 := true, 23 := true][24 := false];
			var v_int_59: int := (match 28 {
				case 6 => 2
				case _ => 18
			});
			var v_DT_1_1_6: DT_1<int, real> := DT_1_1;
			var v_DT_1_1_7: DT_1<int, real> := DT_1_1;
			var v_DT_1_1_8: DT_1<int, real> := DT_1_1;
			var v_DT_1_1_9: DT_1<int, real> := DT_1_1;
			var v_DT_1_1_10: DT_1<int, real> := DT_1_1;
			var v_map_14: map<DT_1<int, real>, bool> := map[v_DT_1_1_6 := false];
			var v_DT_1_1_11: DT_1<int, real> := DT_1_1;
			var v_DT_1_1_12: DT_1<int, real> := v_DT_1_1_11;
			if (if ((v_int_59 in v_map_15)) then (v_map_15[v_int_59]) else ((if ((v_DT_1_1_12 in v_map_14)) then (v_map_14[v_DT_1_1_12]) else (false)))) {
				var v_map_16: map<multiset<int>, bool> := map[multiset{27} := false, multiset({22, -4}) := false, multiset{10, 14, 10} := true, multiset{20} := false];
				var v_multiset_1: multiset<int> := multiset({-18, 19, 29, 3});
				var v_seq_27: seq<int> := [13, -26, -13, 1];
				var v_int_60: int := 29;
				return (if ((if ((v_multiset_1 in v_map_16)) then (v_map_16[v_multiset_1]) else (true))) then ((if ((|v_seq_27| > 0)) then (v_seq_27[v_int_60]) else (5))) else ((if (false) then (14) else (7))));
			} else {
				var v_int_int_1: (int, int) := (2, 1);
				var v_int_int_2: (int, int) := (0, 24);
				var v_int_int_3: (int, int) := (19, 9);
				var v_int_int_4: (int, int) := (1, 18);
				var v_map_17: map<(int, int), bool> := map[v_int_int_1 := true, v_int_int_2 := true, v_int_int_3 := true, v_int_int_4 := false];
				var v_int_int_5: (int, int) := (9, 3);
				var v_int_int_6: (int, int) := v_int_int_5;
				var v_int_int_7: (int, int) := (2, 1);
				var v_int_int_8: (int, int) := (1, 18);
				var v_int_int_9: (int, int) := (19, 9);
				var v_int_int_10: (int, int) := (0, 24);
				var v_DT_1_1_13: DT_1<int, real> := DT_1_1;
				var v_real_bool_bool_8: (real, bool, bool) := (17.67, true, false);
				print "v_int_int_1", " ", v_int_int_1, " ", "v_int_int_2", " ", v_int_int_2, " ", "v_int_int_3", " ", v_int_int_3, " ", "v_int_int_4", " ", v_int_int_4, " ", "v_int_int_5", " ", v_int_int_5, " ", "v_int_int_6", " ", v_int_int_6, " ", "v_map_17", " ", (v_map_17 == map[v_int_int_7 := true, v_int_int_8 := false, v_int_int_9 := true, v_int_int_10 := true]), " ", "v_int_int_1.1", " ", v_int_int_1.1, " ", "v_int_int_2.0", " ", v_int_int_2.0, " ", "v_int_int_1.0", " ", v_int_int_1.0, " ", "v_int_int_3.1", " ", v_int_int_3.1, " ", "v_int_int_4.0", " ", v_int_int_4.0, " ", "v_int_int_2.1", " ", v_int_int_2.1, " ", "v_int_int_3.0", " ", v_int_int_3.0, " ", "v_int_int_5.1", " ", v_int_int_5.1, " ", "v_int_int_4.1", " ", v_int_int_4.1, " ", "v_int_int_5.0", " ", v_int_int_5.0, " ", "v_DT_1_1_7", " ", v_DT_1_1_7, " ", "v_DT_1_1_6", " ", v_DT_1_1_6, " ", "v_DT_1_1_9", " ", v_DT_1_1_9, " ", "v_DT_1_1_8", " ", v_DT_1_1_8, " ", "v_map_15", " ", (v_map_15 == map[23 := true, 24 := false, 14 := true]), " ", "v_int_59", " ", v_int_59, " ", "v_DT_1_1_12", " ", v_DT_1_1_12, " ", "v_DT_1_1_11", " ", v_DT_1_1_11, " ", "v_map_14", " ", (v_map_14 == map[v_DT_1_1_13 := false]), " ", "v_DT_1_1_10", " ", v_DT_1_1_10, " ", "v_seq_25", " ", v_seq_25, " ", "v_int_57", " ", v_int_57, " ", "v_int_56", " ", v_int_56, " ", "v_seq_26", " ", v_seq_26, " ", "v_int_34", " ", v_int_34, " ", "v_int_55", " ", v_int_55, " ", "v_seq_23", " ", v_seq_23, " ", "v_int_37", " ", v_int_37, " ", "v_seq_24", " ", v_seq_24, " ", "v_int_58", " ", v_int_58, " ", "v_int_36", " ", v_int_36, " ", "v_int_52", " ", v_int_52, " ", "v_int_51", " ", v_int_51, " ", "v_array_7[1]", " ", v_array_7[1], " ", "v_map_13", " ", (v_map_13 == map[8 := 28, 11 := 15, 12 := 29]), " ", "v_array_10[1]", " ", v_array_10[1], " ", "v_int_49", " ", v_int_49, " ", "v_int_48", " ", v_int_48, " ", "v_int_47", " ", v_int_47, " ", "v_bool_25", " ", v_bool_25, " ", "v_array_9[4]", " ", v_array_9[4], " ", "v_array_8[3]", " ", v_array_8[3], " ", "v_array_9[0]", " ", v_array_9[0], " ", "v_array_7[0]", " ", v_array_7[0], " ", "v_array_7[2]", " ", v_array_7[2], " ", "v_array_10[0]", " ", v_array_10[0], " ", "v_int_35", " ", v_int_35, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_32", " ", v_int_32, " ", "v_seq_21", " ", v_seq_21, " ", "v_seq_22", " ", v_seq_22, " ", "v_int_37", " ", v_int_37, " ", "v_seq_23", " ", v_seq_23, " ", "v_int_36", " ", v_int_36, " ", "v_array_9[3]", " ", v_array_9[3], " ", "v_array_8[2]", " ", v_array_8[2], " ", "p_m_method_1_1.2", " ", p_m_method_1_1.2, " ", "v_array_11", " ", (v_array_11 == v_array_7), " ", "v_array_10", " ", (v_array_10 == v_array_10), " ", "p_m_method_1_1.0", " ", (p_m_method_1_1.0 == 17.67), " ", "v_array_7[3]", " ", v_array_7[3], " ", "p_m_method_1_1.1", " ", p_m_method_1_1.1, " ", "v_array_10[3]", " ", v_array_10[3], " ", "v_seq_19", " ", v_seq_19, " ", "v_seq_14", " ", (v_seq_14 == ['a', 'v', 'E']), " ", "v_seq_15", " ", v_seq_15, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == v_real_bool_bool_8), " ", "v_seq_12", " ", v_seq_12, " ", "v_seq_13", " ", v_seq_13, " ", "v_array_7", " ", (v_array_7 == v_array_7), " ", "v_array_9[2]", " ", v_array_9[2], " ", "v_array_8", " ", (v_array_8 == v_array_8), " ", "v_array_8[1]", " ", v_array_8[1], " ", "v_array_9", " ", (v_array_9 == v_array_9), " ", "v_char_3", " ", (v_char_3 == 'a'), " ", "v_array_7[4]", " ", v_array_7[4], " ", "v_map_8", " ", (v_map_8 == map[false := v_array_7, true := v_array_8]), " ", "v_array_10[2]", " ", v_array_10[2], " ", "v_int_54", " ", v_int_54, " ", "v_array_8[4]", " ", v_array_8[4], " ", "v_int_53", " ", v_int_53, " ", "v_array_9[1]", " ", v_array_9[1], " ", "v_int_52", " ", v_int_52, " ", "v_array_8[0]", " ", v_array_8[0], "\n";
				return (if ((if ((v_int_int_6 in v_map_17)) then (v_map_17[v_int_int_6]) else (true))) then ((if (true) then (27) else (16))) else ((if (false) then (12) else (23))));
			}
		}
	}
	var v_seq_28: seq<int> := [];
	var v_int_63: int := 7;
	match (if (('h' > 'I')) then ((if ((|v_seq_28| > 0)) then (v_seq_28[v_int_63]) else (19))) else (v_int_52)) {
		case _ => {
			assert true;
			expect true;
			var v_seq_30: seq<int> := ([23] + [-20]);
			var v_seq_29: seq<int> := [-26, 15, 13];
			var v_int_66: int := 29;
			var v_int_67: int := (if ((|v_seq_29| > 0)) then (v_seq_29[v_int_66]) else (19));
			v_array_8[0], v_int_33 := v_array_8[1], (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_67]) else (v_int_33));
			var v_map_20: map<char, int> := map['t' := -5, 'X' := 26, 'z' := 10]['V' := 23];
			var v_char_4: char := (if (true) then ('O') else ('A'));
			var v_seq_31: seq<char> := ['T'];
			var v_int_68: int := 23;
			var v_map_21: map<char, char> := map['B' := 'v', 's' := 'u'];
			var v_char_5: char := 'V';
			var v_seq_32: seq<char> := ['f', 'w', 'E'];
			var v_int_69: int := 15;
			v_int_33, v_bool_25, v_char_4, v_char_3 := (if ((v_char_4 in v_map_20)) then (v_map_20[v_char_4]) else (v_int_54)), ((if ((|v_seq_31| > 0)) then (v_seq_31[v_int_68]) else ('W')) !in (map['x' := 'q', 'T' := 'b', 't' := 'V'] + map['q' := 'e', 'z' := 'a', 'f' := 'D', 'n' := 'A', 'Q' := 'm'])), v_char_3, (match 'e' {
				case _ => (if ((|v_seq_32| > 0)) then (v_seq_32[v_int_69]) else ('l'))
			});
			var v_seq_34: seq<char> := (match 'G' {
				case _ => ['i', 'b', 'o', 'W']
			});
			var v_seq_33: seq<int> := [];
			var v_int_70: int := 1;
			var v_int_71: int := (if ((|v_seq_33| > 0)) then (v_seq_33[v_int_70]) else (21));
			var v_map_22: map<int, char> := map[17 := 'h', 13 := 'g', 21 := 'T'];
			var v_int_72: int := 25;
			var v_map_23: map<char, char> := map['J' := 'Y', 'G' := 'f', 'I' := 'p', 'N' := 'P']['A' := 's'];
			var v_char_6: char := (if (true) then ('e') else ('L'));
			var v_seq_35: seq<char> := ['k', 'l', 'e', 'D'];
			var v_int_73: int := 5;
			v_char_3, v_char_4, v_char_6 := (if ((|v_seq_34| > 0)) then (v_seq_34[v_int_71]) else ((if ((v_int_72 in v_map_22)) then (v_map_22[v_int_72]) else ('Q')))), (match 'A' {
				case _ => (if (false) then ('i') else ('U'))
			}), (if ((v_char_6 in v_map_23)) then (v_map_23[v_char_6]) else ((if ((|v_seq_35| > 0)) then (v_seq_35[v_int_73]) else ('b'))));
			if v_array_8[0] {
				var v_seq_36: seq<int> := [11, 8, 22];
				var v_int_74: int := 16;
				return ((if ((|v_seq_36| > 0)) then (v_seq_36[v_int_74]) else (29)) % v_int_74);
			} else {
				var v_map_24: map<multiset<char>, int> := map[multiset{'R', 'H'} := 4, multiset{'A', 'b', 'w', 'l'} := 20][multiset{'X', 'E', 'R'} := 27];
				var v_multiset_2: multiset<char> := (match 'a' {
					case _ => multiset({'Z', 'L'})
				});
				var v_map_25: map<char, int> := (map['J' := 8, 't' := 11, 'M' := 23, 'd' := 7] - {'x', 'W', 'i', 'y'});
				var v_char_7: char := v_char_3;
				var v_int_76: int, v_int_77: int := (if ((v_multiset_2 in v_map_24)) then (v_map_24[v_multiset_2]) else ((match 'v' {
					case _ => 20
				}))), (if ((v_char_7 in v_map_25)) then (v_map_25[v_char_7]) else (v_int_33));
				for v_int_75 := v_int_76 to v_int_77 
					invariant (v_int_77 - v_int_75 >= 0)
				{
					return v_int_34;
				}
				var v_seq_37: seq<int> := [10, 26, 24, 19];
				var v_int_79: int := 28;
				var v_int_80: int, v_int_81: int := ((if (true) then (7) else (0)) - (if ((|v_seq_37| > 0)) then (v_seq_37[v_int_79]) else (-17))), v_int_73;
				for v_int_78 := v_int_80 to v_int_81 
					invariant (v_int_81 - v_int_78 >= 0)
				{
					
				}
				var v_map_26: map<char, bool> := map['K' := true, 'N' := false, 'F' := false, 'C' := false, 'Q' := true];
				var v_char_8: char := 'S';
				return (if ((if ((v_char_8 in v_map_26)) then (v_map_26[v_char_8]) else (false))) then (v_int_54) else (v_int_61));
			}
		}
		
	}
	
	return v_int_63;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_real_bool_bool_1: (real, bool, bool) := (-8.57, false, false);
	var v_real_bool_bool_2: (real, bool, bool) := (2.15, true, true);
	var v_seq_38: seq<(real, bool, bool)> := [v_real_bool_bool_1, v_real_bool_bool_2];
	var v_int_82: int := 22;
	var v_real_bool_bool_3: (real, bool, bool) := (17.67, true, false);
	var v_real_bool_bool_4: (real, bool, bool) := (if ((match 'I' {
		case 'L' => true
		case _ => false
	})) then ((if ((|v_seq_38| > 0)) then (v_seq_38[v_int_82]) else (v_real_bool_bool_3))) else (v_real_bool_bool_3));
	var v_int_83: int := m_method_1(v_real_bool_bool_4);
	var v_int_7: int := v_int_83;
	var v_seq_39: seq<(real, bool, bool)> := [];
	var v_int_84: int := 28;
	var v_real_bool_bool_5: (real, bool, bool) := (-16.55, true, false);
	var v_real_bool_bool_6: (real, bool, bool) := (if ((|v_seq_39| > 0)) then (v_seq_39[v_int_84]) else (v_real_bool_bool_5));
	var v_int_85: int := m_method_1(v_real_bool_bool_6);
	var v_seq_40: seq<real> := [-6.37];
	var v_int_86: int := 15;
	var v_seq_41: seq<int> := [17];
	var v_seq_42: seq<int> := v_seq_41;
	var v_int_87: int := 21;
	var v_int_88: int := safe_index_seq(v_seq_42, v_int_87);
	var v_int_89: int := v_int_88;
	var v_seq_43: seq<int> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_89 := 2]) else (v_seq_41));
	var v_int_90: int := (19 / 13);
	var v_int_8: int := (match 'e' {
		case 'e' => v_int_85
		case 'l' => ((if ((|v_seq_40| > 0)) then (v_seq_40[v_int_86]) else (27.55))).Floor
		case _ => (if ((|v_seq_43| > 0)) then (v_seq_43[v_int_90]) else ((if (true) then (2) else (-12))))
	});
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8);
	{
		v_int_7 := (v_int_7 + 1);
		return ;
	}
	var v_map_27: map<char, char> := (map['E' := 'i', 'k' := 'e'] - {'p', 'W', 'V'});
	var v_char_9: char := (match 'W' {
		case 'F' => 'c'
		case _ => 'N'
	});
	var v_seq_44: seq<seq<char>> := [['G'], []];
	var v_int_91: int := 15;
	var v_seq_74: seq<seq<char>> := v_seq_44;
	var v_int_136: int := v_int_91;
	var v_int_137: int := safe_index_seq(v_seq_74, v_int_136);
	v_int_91 := v_int_137;
	var v_seq_45: seq<char> := (if ((|v_seq_44| > 0)) then (v_seq_44[v_int_91]) else (['z', 'X', 'D', 'r']));
	var v_int_92: int := (if (false) then (26) else (17));
	var v_map_28: map<char, char> := map['q' := 'c', 'I' := 'q', 'K' := 'O', 'u' := 'E'];
	var v_char_10: char := 'j';
	var v_seq_46: seq<char> := ['b', 'P'];
	var v_seq_75: seq<char> := v_seq_46;
	var v_int_140: int := -27;
	var v_int_141: int := 19;
	var v_int_142: int, v_int_143: int := safe_subsequence(v_seq_75, v_int_140, v_int_141);
	var v_int_138: int, v_int_139: int := v_int_142, v_int_143;
	var v_seq_47: seq<char> := (if ((|v_seq_46| > 0)) then (v_seq_46[v_int_138..v_int_139]) else (v_seq_46));
	var v_int_93: int := (4 - 15);
	var v_map_29: map<char, char> := map['E' := 'P', 'X' := 'C'];
	var v_char_11: char := 'F';
	var v_map_30: map<char, char> := map['b' := 'l', 'Q' := 'T', 'v' := 'S'];
	var v_char_12: char := 'a';
	var v_map_31: map<char, char> := map['U' := 'z'];
	var v_char_13: char := 't';
	var v_seq_48: seq<char> := ['I', 'P'];
	var v_seq_49: seq<char> := v_seq_48;
	var v_int_94: int := 7;
	var v_int_95: int := safe_index_seq(v_seq_49, v_int_94);
	var v_int_96: int := v_int_95;
	var v_seq_52: seq<char> := (if ((|v_seq_48| > 0)) then (v_seq_48[v_int_96 := 'O']) else (v_seq_48));
	var v_seq_77: seq<char> := v_seq_52;
	var v_seq_50: seq<int> := [29];
	var v_int_97: int := 17;
	var v_seq_76: seq<int> := v_seq_50;
	var v_int_144: int := v_int_97;
	var v_int_145: int := safe_index_seq(v_seq_76, v_int_144);
	v_int_97 := v_int_145;
	var v_int_148: int := (if ((|v_seq_50| > 0)) then (v_seq_50[v_int_97]) else (-2));
	var v_seq_51: seq<int> := [];
	var v_int_98: int := 23;
	var v_int_149: int := (if ((|v_seq_51| > 0)) then (v_seq_51[v_int_98]) else (9));
	var v_int_150: int, v_int_151: int := safe_subsequence(v_seq_77, v_int_148, v_int_149);
	var v_int_146: int, v_int_147: int := v_int_150, v_int_151;
	var v_seq_53: seq<char> := (if ((|v_seq_52| > 0)) then (v_seq_52[v_int_146..v_int_147]) else (v_seq_52));
	var v_int_99: int := v_int_98;
	var v_seq_54: seq<char> := ['a'];
	var v_int_100: int := 10;
	var v_seq_55: seq<char> := ['f'];
	var v_int_101: int := 1;
	var v_seq_80: seq<char> := v_seq_55;
	var v_int_156: int := v_int_101;
	var v_int_157: int := safe_index_seq(v_seq_80, v_int_156);
	v_int_101 := v_int_157;
	var v_seq_56: seq<map<char, char>> := [map['P' := 'C', 'A' := 'E']];
	var v_int_102: int := 21;
	var v_seq_78: seq<map<char, char>> := v_seq_56;
	var v_int_152: int := v_int_102;
	var v_int_153: int := safe_index_seq(v_seq_78, v_int_152);
	v_int_102 := v_int_153;
	var v_map_33: map<char, char> := ((if ((|v_seq_56| > 0)) then (v_seq_56[v_int_102]) else (map['D' := 'z', 'X' := 'U'])) + v_map_27);
	var v_seq_57: seq<char> := ['A', 'L'];
	var v_seq_58: seq<char> := v_seq_57;
	var v_int_103: int := 22;
	var v_int_104: int := safe_index_seq(v_seq_58, v_int_103);
	var v_int_105: int := v_int_104;
	var v_seq_59: seq<char> := (if ((|v_seq_57| > 0)) then (v_seq_57[v_int_105 := 'V']) else (v_seq_57));
	var v_int_106: int := v_int_8;
	var v_seq_79: seq<char> := v_seq_59;
	var v_int_154: int := v_int_106;
	var v_int_155: int := safe_index_seq(v_seq_79, v_int_154);
	v_int_106 := v_int_155;
	var v_seq_60: seq<char> := ['C', 'E', 'j'];
	var v_int_107: int := 18;
	var v_char_15: char := (if ((|v_seq_59| > 0)) then (v_seq_59[v_int_106]) else ((if ((|v_seq_60| > 0)) then (v_seq_60[v_int_107]) else ('T'))));
	var v_map_32: map<char, char> := (map['e' := 'I', 'Z' := 't'] + map['U' := 'S', 'R' := 'R', 's' := 'k']);
	var v_char_14: char := v_char_9;
	var v_char_16: char, v_char_17: char, v_char_18: char, v_char_19: char, v_char_20: char := (if (((false <==> false) && v_real_bool_bool_2.2)) then ((if ((v_char_9 in v_map_27)) then (v_map_27[v_char_9]) else ((if (true) then ('c') else ('X'))))) else ((if ((|v_seq_45| > 0)) then (v_seq_45[v_int_92]) else ((if (true) then ('f') else ('Z')))))), (match 'l' {
		case 'S' => (if (v_real_bool_bool_2.1) then ((match 'p' {
			case _ => 'Z'
		})) else ((if ((v_char_10 in v_map_28)) then (v_map_28[v_char_10]) else ('o'))))
		case _ => (if ((|v_seq_47| > 0)) then (v_seq_47[v_int_93]) else (v_char_9))
	}), (match 'F' {
		case 'E' => (if ((if (true) then (false) else (false))) then ((if ((v_char_11 in v_map_29)) then (v_map_29[v_char_11]) else ('d'))) else ((if (false) then ('E') else ('a'))))
		case 'M' => (match 'N' {
			case _ => v_char_9
		})
		case _ => (match 's' {
			case 't' => (match 'w' {
				case _ => 't'
			})
			case _ => (if ((v_char_13 in v_map_31)) then (v_map_31[v_char_13]) else ('E'))
		})
	}), (if ((|v_seq_53| > 0)) then (v_seq_53[v_int_99]) else ((if ((true ==> false)) then ((if ((|v_seq_54| > 0)) then (v_seq_54[v_int_100]) else ('H'))) else ((if ((|v_seq_55| > 0)) then (v_seq_55[v_int_101]) else ('n')))))), (if ((v_char_15 in v_map_33)) then (v_map_33[v_char_15]) else ((if ((v_char_14 in v_map_32)) then (v_map_32[v_char_14]) else ((if (true) then ('d') else ('L'))))));
	var v_map_37: map<char, int> := map['H' := 10, 'o' := -17, 'p' := 16, 'U' := 28, 'G' := 27]['r' := 18][v_char_14 := (match 'l' {
		case 'R' => 13
		case _ => 20
	})];
	var v_seq_61: seq<char> := ['C', 'E', 'a', 'Y'];
	var v_seq_62: seq<char> := v_seq_61;
	var v_int_110: int := 11;
	var v_int_111: int := safe_index_seq(v_seq_62, v_int_110);
	var v_int_112: int := v_int_111;
	var v_seq_63: seq<char> := (if ((|v_seq_61| > 0)) then (v_seq_61[v_int_112 := 'X']) else (v_seq_61));
	var v_int_113: int := (match 'A' {
		case 'u' => 21
		case 'y' => 14
		case _ => 16
	});
	var v_seq_81: seq<char> := v_seq_63;
	var v_int_158: int := v_int_113;
	var v_int_159: int := safe_index_seq(v_seq_81, v_int_158);
	v_int_113 := v_int_159;
	var v_map_34: map<char, char> := map['X' := 'W', 'h' := 's', 'r' := 'y'];
	var v_char_21: char := 'R';
	var v_char_24: char := (if ((|v_seq_63| > 0)) then (v_seq_63[v_int_113]) else ((if ((v_char_21 in v_map_34)) then (v_map_34[v_char_21]) else ('j'))));
	var v_map_36: map<char, int> := (match 'D' {
		case 'v' => map['q' := 11, 'd' := -2, 'U' := 8]
		case _ => map['I' := 17, 'j' := 25]
	});
	var v_map_35: map<char, char> := map['S' := 'U', 'z' := 'x', 'G' := 'd'];
	var v_char_22: char := 'P';
	var v_char_23: char := (if ((v_char_22 in v_map_35)) then (v_map_35[v_char_22]) else ('Q'));
	var v_seq_64: seq<int> := [13];
	var v_int_114: int := 9;
	var v_seq_82: seq<int> := v_seq_64;
	var v_int_160: int := v_int_114;
	var v_int_161: int := safe_index_seq(v_seq_82, v_int_160);
	v_int_114 := v_int_161;
	var v_int_108: int := (if ((v_char_24 in v_map_37)) then (v_map_37[v_char_24]) else ((if ((v_char_23 in v_map_36)) then (v_map_36[v_char_23]) else ((if ((|v_seq_64| > 0)) then (v_seq_64[v_int_114]) else (20))))));
	var v_map_38: map<char, int> := map['l' := 11, 'C' := 22, 'n' := 23];
	var v_char_25: char := 'c';
	var v_int_109: int := (match 'b' {
		case 'V' => v_int_95
		case 'O' => v_int_8
		case _ => (if (v_real_bool_bool_2.1) then ((if ((v_char_25 in v_map_38)) then (v_map_38[v_char_25]) else (9))) else (v_int_102))
	});
	while (v_int_108 < v_int_109) 
		decreases v_int_109 - v_int_108;
		invariant (v_int_108 <= v_int_109);
	{
		v_int_108 := (v_int_108 + 1);
		var v_map_39: map<char, map<char, bool>> := map['v' := map['I' := true, 'E' := true, 'm' := false], 'r' := map['H' := false, 'B' := false], 'B' := map['n' := true], 'p' := map['V' := true, 'n' := false, 'a' := true, 'K' := false]];
		var v_char_26: char := 'h';
		var v_map_40: map<char, bool> := (if ((if (false) then (true) else (true))) then ((if ((v_char_26 in v_map_39)) then (v_map_39[v_char_26]) else (map['i' := true, 'H' := true, 'n' := false, 'p' := false, 'N' := true]))) else ((match 'Z' {
			case _ => map['S' := false, 'O' := true, 'Z' := false, 'P' := false]
		})));
		var v_char_27: char := (match 'l' {
			case _ => (match 'V' {
				case _ => 'j'
			})
		});
		var v_seq_65: seq<bool> := [false, true, false, true];
		var v_int_115: int := 18;
		if (if ((v_char_27 in v_map_40)) then (v_map_40[v_char_27]) else ((match 'D' {
			case _ => (if ((|v_seq_65| > 0)) then (v_seq_65[v_int_115]) else (false))
		}))) {
			
		} else {
			return ;
		}
		break;
	}
	var v_real_bool_bool_9: (real, bool, bool) := (17.67, true, false);
	var v_real_bool_bool_10: (real, bool, bool) := (-8.57, false, false);
	var v_real_bool_bool_11: (real, bool, bool) := (2.15, true, true);
	var v_real_bool_bool_12: (real, bool, bool) := (17.67, true, false);
	var v_real_bool_bool_13: (real, bool, bool) := (-8.57, false, false);
	var v_real_bool_bool_14: (real, bool, bool) := (2.15, true, true);
	print "v_real_bool_bool_4", " ", (v_real_bool_bool_4 == v_real_bool_bool_9), " ", "v_real_bool_bool_1", " ", (v_real_bool_bool_1 == v_real_bool_bool_10), " ", "v_real_bool_bool_2", " ", (v_real_bool_bool_2 == v_real_bool_bool_11), " ", "v_real_bool_bool_3", " ", (v_real_bool_bool_3 == v_real_bool_bool_12), " ", "v_int_104", " ", v_int_104, " ", "v_int_105", " ", v_int_105, " ", "v_seq_38", " ", (v_seq_38 == [v_real_bool_bool_13, v_real_bool_bool_14]), " ", "v_int_106", " ", v_int_106, " ", "v_int_107", " ", v_int_107, " ", "v_int_100", " ", v_int_100, " ", "v_int_101", " ", v_int_101, " ", "v_int_102", " ", v_int_102, " ", "v_int_103", " ", v_int_103, " ", "v_int_82", " ", v_int_82, " ", "v_int_83", " ", v_int_83, " ", "v_real_bool_bool_1.0", " ", (v_real_bool_bool_1.0 == -8.57), " ", "v_real_bool_bool_3.1", " ", v_real_bool_bool_3.1, " ", "v_real_bool_bool_3.2", " ", v_real_bool_bool_3.2, " ", "v_char_24", " ", (v_char_24 == 'X'), " ", "v_real_bool_bool_1.1", " ", v_real_bool_bool_1.1, " ", "v_char_23", " ", (v_char_23 == 'Q'), " ", "v_real_bool_bool_1.2", " ", v_real_bool_bool_1.2, " ", "v_real_bool_bool_3.0", " ", (v_real_bool_bool_3.0 == 17.67), " ", "v_char_22", " ", (v_char_22 == 'P'), " ", "v_int_108", " ", v_int_108, " ", "v_int_109", " ", v_int_109, " ", "v_int_111", " ", v_int_111, " ", "v_int_112", " ", v_int_112, " ", "v_int_113", " ", v_int_113, " ", "v_map_27", " ", (v_map_27 == map['E' := 'i', 'k' := 'e']), " ", "v_int_114", " ", v_int_114, " ", "v_seq_61", " ", (v_seq_61 == ['C', 'E', 'a', 'Y']), " ", "v_seq_62", " ", (v_seq_62 == ['C', 'E', 'a', 'Y']), " ", "v_seq_63", " ", (v_seq_63 == ['X', 'E', 'a', 'Y']), " ", "v_int_110", " ", v_int_110, " ", "v_seq_64", " ", v_seq_64, " ", "v_seq_60", " ", (v_seq_60 == ['C', 'E', 'j']), " ", "v_char_18", " ", (v_char_18 == 'E'), " ", "v_char_17", " ", (v_char_17 == 'N'), " ", "v_char_16", " ", (v_char_16 == 'c'), " ", "v_char_15", " ", (v_char_15 == 'V'), " ", "v_char_14", " ", (v_char_14 == 'N'), " ", "v_map_35", " ", (v_map_35 == map['S' := 'U', 'G' := 'd', 'z' := 'x']), " ", "v_map_36", " ", (v_map_36 == map['I' := 17, 'j' := 25]), " ", "v_map_33", " ", (v_map_33 == map['P' := 'C', 'A' := 'E', 'E' := 'i', 'k' := 'e']), " ", "v_map_34", " ", (v_map_34 == map['r' := 'y', 'X' := 'W', 'h' := 's']), " ", "v_map_32", " ", (v_map_32 == map['R' := 'R', 's' := 'k', 'e' := 'I', 'U' := 'S', 'Z' := 't']), " ", "v_char_19", " ", (v_char_19 == 'f'), " ", "v_seq_58", " ", (v_seq_58 == ['A', 'L']), " ", "v_seq_59", " ", (v_seq_59 == ['V', 'L']), " ", "v_seq_54", " ", (v_seq_54 == ['a']), " ", "v_seq_55", " ", (v_seq_55 == ['f']), " ", "v_seq_56", " ", (v_seq_56 == [map['P' := 'C', 'A' := 'E']]), " ", "v_map_37", " ", (v_map_37 == map['p' := 16, 'r' := 18, 'U' := 28, 'G' := 27, 'H' := 10, 'N' := 20, 'o' := -17]), " ", "v_seq_57", " ", (v_seq_57 == ['A', 'L']), " ", "v_seq_50", " ", v_seq_50, " ", "v_char_21", " ", (v_char_21 == 'R'), " ", "v_seq_51", " ", v_seq_51, " ", "v_char_20", " ", (v_char_20 == 'd'), " ", "v_seq_52", " ", (v_seq_52 == ['O', 'P']), " ", "v_seq_53", " ", (v_seq_53 == []), " ", "v_real_bool_bool_2.2", " ", v_real_bool_bool_2.2, " ", "v_real_bool_bool_2.0", " ", (v_real_bool_bool_2.0 == 2.15), " ", "v_real_bool_bool_2.1", " ", v_real_bool_bool_2.1, " ", "v_int_8", " ", v_int_8, " ", "v_char_9", " ", (v_char_9 == 'N'), " ", "v_int_7", " ", v_int_7, " ", "v_seq_48", " ", (v_seq_48 == ['I', 'P']), " ", "v_seq_49", " ", (v_seq_49 == ['I', 'P']), " ", "v_int_99", " ", v_int_99, " ", "v_int_98", " ", v_int_98, " ", "v_seq_44", " ", (v_seq_44 == [['G'], []]), " ", "v_seq_45", " ", (v_seq_45 == ['G']), " ", "v_int_92", " ", v_int_92, " ", "v_int_91", " ", v_int_91, " ", "v_int_97", " ", v_int_97, " ", "v_int_96", " ", v_int_96, " ", "v_int_95", " ", v_int_95, " ", "v_int_94", " ", v_int_94, "\n";
}

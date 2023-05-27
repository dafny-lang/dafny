// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1
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

method m_method_6(p_m_method_6_1: int, p_m_method_6_2: int) returns (ret_1: map<int, int>)
{
	match p_m_method_6_1 {
		case _ => {
			
		}
		
	}
	
	var v_seq_14: seq<int> := [];
	var v_int_49: int := 21;
	var v_int_51: int, v_int_52: int := (if (true) then (20) else (26)), (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_49]) else (11));
	for v_int_48 := v_int_51 to v_int_52 
		invariant (v_int_52 - v_int_48 >= 0)
	{
		var v_map_5: map<int, map<int, int>> := map[7 := map[14 := -3, 6 := 25, 29 := 23, 18 := 14, 19 := 13], 5 := map[-28 := 29, 29 := 21, 6 := 9], -9 := map[6 := 2, 0 := 25, 28 := 24], 21 := map[20 := 12, 9 := 17, -20 := 7, 29 := 29, 25 := 21], 7 := map[25 := -12, 9 := 27, 8 := 22]];
		var v_int_50: int := 21;
		return (if ((v_int_50 in v_map_5)) then (v_map_5[v_int_50]) else (map[2 := 23, 23 := -17, 9 := 8]));
	}
	return map[15 := 25, 6 := 18, 5 := 12, 20 := 29, 2 := -17][19 := 27];
}

method m_method_5(p_m_method_5_1: int, p_m_method_5_2: int, p_m_method_5_3: int) returns (ret_1: seq<int>)
	requires ((p_m_method_5_1 == 4) && (p_m_method_5_3 == 1) && (p_m_method_5_2 == 9));
	ensures (((p_m_method_5_1 == 4) && (p_m_method_5_3 == 1) && (p_m_method_5_2 == 9)) ==> (|ret_1| == 4 && (ret_1[0] == -10) && (ret_1[1] == 9) && (ret_1[2] == 3) && (ret_1[3] == -21)));
{
	assert ((p_m_method_5_3 == 1));
	expect ((p_m_method_5_3 == 1));
	var v_int_14: int := 13;
	var v_int_15: int := 23;
	while (v_int_14 < v_int_15) 
		decreases v_int_15 - v_int_14;
		invariant (v_int_14 <= v_int_15);
	{
		v_int_14 := (v_int_14 + 1);
		assert ((v_int_15 == 23) && (p_m_method_5_3 == 1));
		expect ((v_int_15 == 23) && (p_m_method_5_3 == 1));
		var v_int_16: int, v_int_17: int, v_int_18: int, v_int_19: int, v_int_20: int := 10, 21, 18, 6, 18;
		var v_int_22: int, v_int_23: int := 20, 2;
		for v_int_21 := v_int_22 downto v_int_23 
			invariant (v_int_21 - v_int_23 >= 0)
		{
			print "v_int_21", " ", v_int_21, " ", "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_int_20", " ", v_int_20, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "p_m_method_5_3", " ", p_m_method_5_3, " ", "p_m_method_5_2", " ", p_m_method_5_2, " ", "p_m_method_5_1", " ", p_m_method_5_1, "\n";
			return [-10, 9, 3, -21];
		}
		v_int_19, v_int_18 := 24, 17;
		v_int_17, v_int_20 := 2, 9;
	}
	match 28 {
		case _ => {
			return [25, 26, 6];
		}
		
	}
	
}

method m_method_4(p_m_method_4_1: array<real>, p_m_method_4_2: seq<int>) returns (ret_1: real)
	requires (|p_m_method_4_2| == 0 && p_m_method_4_1.Length == 5 && (15.22 < p_m_method_4_1[0] < 15.42) && (23.32 < p_m_method_4_1[1] < 23.52) && (-0.17 < p_m_method_4_1[2] < 0.03) && (-5.41 < p_m_method_4_1[3] < -5.21) && (18.74 < p_m_method_4_1[4] < 18.94));
	ensures ((|p_m_method_4_2| == 0 && p_m_method_4_1.Length == 5 && (15.22 < p_m_method_4_1[0] < 15.42) && (23.32 < p_m_method_4_1[1] < 23.52) && (-0.17 < p_m_method_4_1[2] < 0.03) && (-5.41 < p_m_method_4_1[3] < -5.21) && (18.74 < p_m_method_4_1[4] < 18.94)) ==> ((27.89 < ret_1 < 28.09)));
{
	print "p_m_method_4_1[0]", " ", (p_m_method_4_1[0] == 15.32), " ", "p_m_method_4_1", " ", "p_m_method_4_1[1]", " ", (p_m_method_4_1[1] == 23.42), " ", "p_m_method_4_1[2]", " ", (p_m_method_4_1[2] == -0.07), " ", "p_m_method_4_2", " ", p_m_method_4_2, "\n";
	return 27.99;
}

method m_method_3(p_m_method_3_1: bool, p_m_method_3_2: (int, int)) returns (ret_1: real)
	requires ((p_m_method_3_1 == false) && ((p_m_method_3_2).0 == 25) && ((p_m_method_3_2).1 == 23));
	ensures (((p_m_method_3_1 == false) && ((p_m_method_3_2).0 == 25) && ((p_m_method_3_2).1 == 23)) ==> ((27.89 < ret_1 < 28.09)));
{
	var v_multiset_int_char_1: (multiset<real>, int, char) := (multiset{-4.75}, 2, 'q');
	var v_multiset_int_char_2: (multiset<real>, int, char) := (multiset{1.71, 16.85, 13.18}, 15, 'w');
	var v_multiset_int_char_3: (multiset<real>, int, char), v_bool_1: bool, v_int_7: int, v_multiset_1: multiset<seq<int>> := (if (false) then (v_multiset_int_char_1) else (v_multiset_int_char_2)), false, (15 * 11), multiset({[], [20, 8, 19], [], []});
	var v_array_1: array<real> := new real[5] [15.32, 23.42, -0.07, -5.31, 18.84];
	var v_array_2: array<real> := v_array_1;
	var v_seq_3: seq<int> := [];
	var v_real_2: real := m_method_4(v_array_2, v_seq_3);
	var v_multiset_int_char_4: (multiset<real>, int, char) := (multiset{1.71, 13.18, 16.85}, 15, 'w');
	var v_multiset_int_char_5: (multiset<real>, int, char) := (multiset{1.71, 13.18, 16.85}, 15, 'w');
	var v_multiset_int_char_6: (multiset<real>, int, char) := (multiset{-4.75}, 2, 'q');
	print "v_bool_1", " ", v_bool_1, " ", "v_multiset_int_char_3", " ", (v_multiset_int_char_3 == v_multiset_int_char_4), " ", "v_multiset_int_char_2", " ", (v_multiset_int_char_2 == v_multiset_int_char_5), " ", "v_multiset_int_char_1", " ", (v_multiset_int_char_1 == v_multiset_int_char_6), " ", "v_multiset_int_char_1.0", " ", (v_multiset_int_char_1.0 == multiset{-4.75}), " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_1), " ", "v_array_1[2]", " ", (v_array_1[2] == -0.07), " ", "v_array_1[0]", " ", (v_array_1[0] == 15.32), " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "v_multiset_int_char_1.2", " ", (v_multiset_int_char_1.2 == 'q'), " ", "v_multiset_int_char_2.1", " ", v_multiset_int_char_2.1, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "v_multiset_int_char_1.1", " ", v_multiset_int_char_1.1, " ", "v_multiset_int_char_2.0", " ", (v_multiset_int_char_2.0 == multiset{1.71, 13.18, 16.85}), " ", "v_multiset_int_char_2.2", " ", (v_multiset_int_char_2.2 == 'w'), " ", "v_array_1[4]", " ", (v_array_1[4] == 18.84), " ", "v_int_7", " ", v_int_7, " ", "p_m_method_3_2.1", " ", p_m_method_3_2.1, " ", "v_multiset_1", " ", (v_multiset_1 == multiset{[], [20, 8, 19]}), " ", "p_m_method_3_2.0", " ", p_m_method_3_2.0, " ", "v_seq_3", " ", v_seq_3, " ", "v_array_1[1]", " ", (v_array_1[1] == 23.42), " ", "v_real_2", " ", (v_real_2 == 27.99), " ", "v_array_1[3]", " ", (v_array_1[3] == -5.31), "\n";
	return v_real_2;
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

method m_method_2(p_m_method_2_1: real) returns (ret_1: char)
	requires ((15.25 < p_m_method_2_1 < 15.45));
	ensures (((15.25 < p_m_method_2_1 < 15.45)) ==> ((ret_1 == 'o')));
{
	print "p_m_method_2_1", " ", (p_m_method_2_1 == 15.35), "\n";
	return 'o';
}

method m_method_1(p_m_method_1_1: real) returns (ret_1: bool)
	requires ((-0.57 < p_m_method_1_1 < -0.37)) || ((27.89 < p_m_method_1_1 < 28.09));
	ensures (((-0.57 < p_m_method_1_1 < -0.37)) ==> ((ret_1 == true))) && (((27.89 < p_m_method_1_1 < 28.09)) ==> ((ret_1 == true)));
{
	var v_map_1: map<char, bool> := (map['d' := true, 'm' := true] - {});
	var v_real_1: real := 15.35;
	var v_char_1: char := m_method_2(v_real_1);
	var v_char_2: char := v_char_1;
	print "v_char_1", " ", (v_char_1 == 'o'), " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 27.99), " ", "v_char_2", " ", (v_char_2 == 'o'), " ", "v_real_1", " ", (v_real_1 == 15.35), " ", "v_map_1", " ", (v_map_1 == map['d' := true, 'm' := true]), "\n";
	return (if ((v_char_2 in v_map_1)) then (v_map_1[v_char_2]) else (('l' > 'N')));
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_seq_4: seq<bool> := [false, false, false];
	var v_int_8: int := -7;
	var v_seq_72: seq<bool> := v_seq_4;
	var v_int_126: int := v_int_8;
	var v_int_127: int := safe_index_seq(v_seq_72, v_int_126);
	v_int_8 := v_int_127;
	var v_bool_2: bool := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_8]) else (true));
	var v_int_int_1: (int, int) := (25, 23);
	var v_int_int_2: (int, int) := (27, 22);
	var v_int_int_3: (int, int) := (3, 10);
	var v_seq_5: seq<(int, int)> := [v_int_int_1, v_int_int_2, v_int_int_3];
	var v_int_9: int := 16;
	var v_seq_73: seq<(int, int)> := v_seq_5;
	var v_int_128: int := v_int_9;
	var v_int_129: int := safe_index_seq(v_seq_73, v_int_128);
	v_int_9 := v_int_129;
	var v_int_int_4: (int, int) := (24, 10);
	var v_int_int_5: (int, int) := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_9]) else (v_int_int_4));
	var v_real_3: real := m_method_3(v_bool_2, v_int_int_5);
	var v_real_4: real := v_real_3;
	var v_bool_3: bool := m_method_1(v_real_4);
	if v_bool_3 {
		assert ((v_int_int_4.1 == 10) && (v_int_int_1.1 == 23));
		expect ((v_int_int_4.1 == 10) && (v_int_int_1.1 == 23));
		var v_real_5: real := v_real_4;
		var v_bool_4: bool := m_method_1(v_real_5);
		var v_map_2: map<int, multiset<char>> := (map[8 := multiset{}] + map[8 := multiset{}, 12 := multiset{'x'}, 4 := multiset{'W', 'c', 'K', 's'}]);
		var v_int_10: int := (24 + 16);
		var v_seq_6: seq<multiset<multiset<bool>>> := [multiset{}, multiset{multiset{false, false, false}, multiset({false}), multiset{true, false, true, false}, multiset({true})}];
		var v_seq_74: seq<multiset<multiset<bool>>> := v_seq_6;
		var v_int_132: int := 27;
		var v_int_133: int := 3;
		var v_int_134: int, v_int_135: int := safe_subsequence(v_seq_74, v_int_132, v_int_133);
		var v_int_130: int, v_int_131: int := v_int_134, v_int_135;
		var v_seq_7: seq<multiset<multiset<bool>>> := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_130..v_int_131]) else (v_seq_6));
		var v_int_11: int := v_int_8;
		var v_seq_8: seq<multiset<multiset<bool>>> := ([multiset({multiset({}), multiset{}, multiset{true, true, true, true}, multiset{true, true}})] + [multiset{}]);
		var v_int_12: int := v_int_int_3.1;
		var v_map_3: map<int, multiset<multiset<bool>>> := map[17 := multiset{multiset{false, false, false}, multiset{true}, multiset{false}, multiset{true}}, 5 := multiset{multiset{false, false}, multiset({}), multiset{true}}, 19 := multiset({}), 1 := multiset{}];
		var v_int_13: int := 8;
		var v_seq_11: seq<multiset<multiset<int>>> := (if ((false <==> true)) then (([multiset{}, multiset({multiset({29, 25})})] + [multiset{multiset{-26, 27, 27}}])) else ((if (true) then ([multiset{multiset{}, multiset{0}, multiset{20}, multiset({})}, multiset{multiset{0, 9}, multiset{6, 22, 6}, multiset({28}), multiset{14, 13, 28}}, multiset({})]) else ([multiset{}, multiset{multiset({14, -4}), multiset({24, 24, 22, 26})}, multiset{multiset{19, 18, -1}, multiset{-13, 20, 29}}, multiset{multiset{25}, multiset({3, 5}), multiset({-15}), multiset{}}]))));
		var v_int_29: int := 4;
		var v_int_30: int := 9;
		var v_int_31: int := 1;
		var v_seq_9: seq<int> := m_method_5(v_int_29, v_int_30, v_int_31);
		var v_seq_10: seq<int> := v_seq_9;
		var v_int_32: int := 6;
		var v_int_33: int := 1;
		var v_int_34: int := safe_modulus(v_int_32, v_int_33);
		var v_int_35: int := v_int_34;
		var v_int_36: int := (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_35]) else ((match 14 {
			case _ => 20
		})));
		var v_seq_75: seq<multiset<multiset<int>>> := v_seq_11;
		var v_int_136: int := v_int_36;
		var v_int_137: int := safe_index_seq(v_seq_75, v_int_136);
		v_int_36 := v_int_137;
		var v_seq_12: seq<multiset<multiset<int>>> := v_seq_11;
		var v_int_37: int := v_int_int_3.0;
		var v_bool_5: bool, v_multiset_2: multiset<char>, v_multiset_3: multiset<multiset<bool>>, v_multiset_4: multiset<multiset<int>> := v_bool_4, ((if ((v_int_10 in v_map_2)) then (v_map_2[v_int_10]) else ((multiset({}) + multiset{'b', 't'}))) + (multiset({'m', 'c', 'N', 's'}) + (if (false) then (multiset{'E', 'q', 'Y', 'Y'}) else (multiset{'A', 'N', 'I', 'g'})))), (match 26 {
			case 18 => (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_11]) else ((multiset{multiset{true, false, false}, multiset{true, false, true}} - multiset({multiset{}, multiset{false, false}, multiset({true})}))))
			case _ => (match 16 {
				case 16 => (multiset{} + multiset{multiset{true, true, true}})
				case _ => (if ((v_int_13 in v_map_3)) then (v_map_3[v_int_13]) else (multiset({multiset{true, false, false}, multiset({}), multiset({false, true, false, false})})))
			})
		}), (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_36]) else ((if ((|v_seq_12| > 0)) then (v_seq_12[v_int_37]) else ((match 12 {
			case _ => multiset({multiset{19, 15, 6}, multiset{11}})
		})))));
		var v_seq_13: seq<int> := v_seq_10;
		var v_int_38: int := 23;
		var v_int_39: int := 12;
		var v_int_40: int := safe_division(v_int_38, v_int_39);
		var v_int_41: int := v_int_40;
		var v_int_42: int := v_int_39;
		var v_int_43: int := safe_modulus(v_int_41, v_int_42);
		var v_int_44: int := v_int_43;
		var v_real_6: real := -0.47;
		var v_bool_6: bool := m_method_1(v_real_6);
		var v_map_4: map<int, int> := map[21 := 20, 6 := 2, 17 := 21, 8 := 21, 22 := 12];
		var v_int_45: int := 10;
		v_int_29, v_int_42, v_int_43 := (if ((|v_seq_13| > 0)) then (v_seq_13[v_int_44]) else ((if (v_bool_6) then ((if (false) then (1) else (16))) else ((if ((v_int_45 in v_map_4)) then (v_map_4[v_int_45]) else (14)))))), v_int_30, v_int_37;
		print "v_bool_5", " ", v_bool_5, " ", "v_bool_4", " ", v_bool_4, " ", "v_bool_6", " ", v_bool_6, " ", "v_int_45", " ", v_int_45, " ", "v_int_44", " ", v_int_44, " ", "v_int_43", " ", v_int_43, " ", "v_seq_10", " ", v_seq_10, " ", "v_seq_11", " ", (v_seq_11 == [multiset{multiset{}, multiset{}, multiset{0}, multiset{20}}, multiset{multiset{28, 13, 14}, multiset{0, 9}, multiset{6, 6, 22}, multiset{28}}, multiset{}]), " ", "v_seq_12", " ", (v_seq_12 == [multiset{multiset{}, multiset{}, multiset{0}, multiset{20}}, multiset{multiset{28, 13, 14}, multiset{0, 9}, multiset{6, 6, 22}, multiset{28}}, multiset{}]), " ", "v_seq_13", " ", v_seq_13, " ", "v_int_42", " ", v_int_42, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, " ", "v_map_4", " ", (v_map_4 == map[17 := 21, 21 := 20, 6 := 2, 22 := 12, 8 := 21]), " ", "v_multiset_4", " ", (v_multiset_4 == multiset{multiset{}, multiset{}, multiset{0}, multiset{20}}), " ", "v_multiset_3", " ", (v_multiset_3 == multiset{multiset{true, true, true}}), " ", "v_multiset_2", " ", (v_multiset_2 == multiset{'A', 'b', 'c', 's', 't', 'g', 'I', 'm', 'N', 'N'}), " ", "v_int_29", " ", v_int_29, " ", "v_map_2", " ", (v_map_2 == map[4 := multiset{'c', 's', 'W', 'K'}, 8 := multiset{}, 12 := multiset{'x'}]), " ", "v_seq_9", " ", v_seq_9, " ", "v_int_35", " ", v_int_35, " ", "v_int_34", " ", v_int_34, " ", "v_int_33", " ", v_int_33, " ", "v_int_10", " ", v_int_10, " ", "v_int_32", " ", v_int_32, " ", "v_int_39", " ", v_int_39, " ", "v_int_38", " ", v_int_38, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_int_31", " ", v_int_31, " ", "v_real_5", " ", (v_real_5 == 27.99), " ", "v_int_30", " ", v_int_30, " ", "v_real_6", " ", (v_real_6 == -0.47), " ", "v_int_int_1", " ", v_int_int_1, " ", "v_int_int_2", " ", v_int_int_2, " ", "v_int_int_3", " ", v_int_int_3, " ", "v_bool_3", " ", v_bool_3, " ", "v_int_int_4", " ", v_int_int_4, " ", "v_bool_2", " ", v_bool_2, " ", "v_int_int_5", " ", v_int_int_5, " ", "v_int_8", " ", v_int_8, " ", "v_seq_5", " ", v_seq_5, " ", "v_seq_4", " ", v_seq_4, " ", "v_int_9", " ", v_int_9, " ", "v_int_int_1.1", " ", v_int_int_1.1, " ", "v_int_int_2.0", " ", v_int_int_2.0, " ", "v_int_int_1.0", " ", v_int_int_1.0, " ", "v_real_3", " ", (v_real_3 == 27.99), " ", "v_int_int_3.1", " ", v_int_int_3.1, " ", "v_int_int_4.0", " ", v_int_int_4.0, " ", "v_real_4", " ", (v_real_4 == 27.99), " ", "v_int_int_2.1", " ", v_int_int_2.1, " ", "v_int_int_3.0", " ", v_int_int_3.0, " ", "v_int_int_4.1", " ", v_int_int_4.1, "\n";
		return ;
	}
	var v_int_46: int := (v_int_int_1.0 / v_int_int_4.1);
	var v_int_53: int := v_int_8;
	var v_array_3: array<char> := new char[3] ['B', 'G', 'u'];
	var v_int_54: int := v_array_3.Length;
	var v_map_6: map<int, int> := m_method_6(v_int_53, v_int_54);
	var v_map_8: map<int, int> := v_map_6;
	var v_int_58: int := v_int_int_4.1;
	var v_int_55: int := v_int_53;
	var v_map_7: map<char, int> := map['R' := 14, 'V' := 13, 'L' := 16];
	var v_char_3: char := 'n';
	var v_int_56: int := (if ((v_char_3 in v_map_7)) then (v_map_7[v_char_3]) else (26));
	var v_int_57: int := safe_division(v_int_55, v_int_56);
	var v_int_47: int := (if ((v_int_58 in v_map_8)) then (v_map_8[v_int_58]) else (v_int_57));
	while (v_int_46 < v_int_47) 
		decreases v_int_47 - v_int_46;
		invariant (v_int_46 <= v_int_47);
	{
		v_int_46 := (v_int_46 + 1);
		continue;
	}
	var v_seq_15: seq<real> := [23.76];
	var v_int_61: int := 5;
	var v_int_59: int := ((match 'H' {
		case _ => v_real_3
	})).Floor;
	var v_seq_16: seq<int> := ([] + [23]);
	var v_int_62: int := v_int_59;
	var v_int_60: int := (if ((v_bool_3 || (if (false) then (true) else (false)))) then (v_int_int_4.0) else ((if ((|v_seq_16| > 0)) then (v_seq_16[v_int_62]) else ((-28 % 11)))));
	while (v_int_59 < v_int_60) 
		decreases v_int_60 - v_int_59;
		invariant (v_int_59 <= v_int_60);
	{
		v_int_59 := (v_int_59 + 1);
		return ;
	}
	var v_map_9: map<char, map<char, seq<bool>>> := map['d' := map['j' := [true, true, false], 'Z' := [], 'V' := [true, false, false, false], 'z' := [false, false]]];
	var v_char_4: char := 'h';
	var v_map_10: map<char, seq<bool>> := (if ((v_char_4 in v_map_9)) then (v_map_9[v_char_4]) else (map['y' := []]));
	var v_char_5: char := (match 'v' {
		case _ => 'h'
	});
	var v_seq_17: seq<bool> := (if ((v_char_5 in v_map_10)) then (v_map_10[v_char_5]) else (v_seq_4));
	var v_int_63: int := ((27 + 28) / (match 'k' {
		case _ => 23
	}));
	var v_map_11: map<char, bool> := map['K' := false, 'd' := false, 'U' := true];
	var v_char_6: char := 'A';
	if (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_63]) else ((if (v_bool_2) then (v_bool_2) else ((if ((v_char_6 in v_map_11)) then (v_map_11[v_char_6]) else (true)))))) {
		
	} else {
		if (if (v_bool_3) then (!(!(false))) else (v_bool_3)) {
			var v_seq_18: seq<map<char, char>> := [map['d' := 'l', 'K' := 'T', 'M' := 'D'], map['u' := 'n', 'F' := 'i', 'Q' := 'H', 'i' := 'H'], map['v' := 'I'], map['S' := 'a', 'T' := 'w']];
			var v_int_64: int := 8;
			var v_map_12: map<char, char> := (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_64]) else (map['h' := 'V', 'G' := 'e', 'Z' := 'm', 'k' := 'z', 'x' := 'U']));
			var v_char_7: char := v_char_4;
			var v_map_13: map<char, seq<char>> := map['Y' := ['j', 'R', 'I']];
			var v_char_8: char := 'B';
			var v_seq_19: seq<char> := (if ((v_char_8 in v_map_13)) then (v_map_13[v_char_8]) else ([]));
			var v_int_65: int := (match 'i' {
				case _ => 17
			});
			var v_map_14: map<char, char> := map['O' := 'W', 'l' := 'X'];
			var v_char_9: char := 'I';
			v_char_6 := (match 'g' {
				case _ => (if ((|v_seq_19| > 0)) then (v_seq_19[v_int_65]) else ((if ((v_char_9 in v_map_14)) then (v_map_14[v_char_9]) else ('d'))))
			});
			if v_bool_3 {
				var v_seq_20: seq<bool> := [true, true, false, true];
				var v_int_66: int := 2;
				var v_map_15: map<char, map<char, char>> := map['P' := map['F' := 'C'], 'g' := map['s' := 'M', 'x' := 'g', 'y' := 'a', 'L' := 'i', 'n' := 'T'], 'w' := map['q' := 'V', 'b' := 'J', 'a' := 'r', 'C' := 'u', 'c' := 'k'], 'o' := map['g' := 'f', 'e' := 'v', 'Y' := 's', 'o' := 'D'], 'y' := map['A' := 'V', 'c' := 'O', 'm' := 'k', 'e' := 'I']];
				var v_char_10: char := 'c';
				var v_map_17: map<char, char> := (if ((v_char_10 in v_map_15)) then (v_map_15[v_char_10]) else (map['I' := 'Q']));
				var v_seq_21: seq<char> := ['V', 'Z'];
				var v_int_67: int := 18;
				var v_char_12: char := (if ((|v_seq_21| > 0)) then (v_seq_21[v_int_67]) else ('l'));
				var v_map_16: map<char, char> := map['h' := 'z', 'k' := 'G'];
				var v_char_11: char := 'j';
				var v_seq_22: seq<char> := ['K'];
				var v_int_68: int := 9;
				var v_seq_23: seq<char> := ['x', 'H', 'Z'];
				var v_seq_25: seq<char> := ((if ((|v_seq_23| > 0)) then (v_seq_23[5..0]) else (v_seq_23)) + (['X', 's', 'n'] + []));
				var v_seq_24: seq<int> := [21, 1, 23];
				var v_int_69: int := 26;
				var v_int_70: int := ((2 / 23) - (if ((|v_seq_24| > 0)) then (v_seq_24[v_int_69]) else (6)));
				var v_map_18: map<char, char> := map['R' := 'v', 'C' := 'd'];
				var v_char_13: char := 'A';
				v_char_11, v_char_5, v_char_6, v_char_3 := (if ((if ((if ((|v_seq_20| > 0)) then (v_seq_20[v_int_66]) else (true))) then ((if (true) then (false) else (false))) else ((false || true)))) then ((if ((v_char_12 in v_map_17)) then (v_map_17[v_char_12]) else ((if ((v_char_11 in v_map_16)) then (v_map_16[v_char_11]) else ('F'))))) else ((match 'O' {
					case _ => (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_68]) else ('h'))
				}))), v_char_10, (if ((|v_seq_25| > 0)) then (v_seq_25[v_int_70]) else ((if (!(true)) then (v_char_10) else ((if ((v_char_13 in v_map_18)) then (v_map_18[v_char_13]) else ('h')))))), v_array_3[1];
				assert true;
				expect true;
				return ;
			} else {
				
			}
			if v_bool_2 {
				return ;
			}
		} else {
			return ;
		}
		var v_seq_26: seq<bool> := v_seq_4;
		var v_int_71: int := ((if (false) then (28) else (15)) % (10 - 1));
		var v_seq_27: seq<seq<bool>> := [[false], [true], [true, true], [true, false]];
		var v_int_72: int := 27;
		var v_seq_28: seq<bool> := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_72]) else ([true]));
		var v_int_73: int := (if (false) then (-6) else (5));
		if (if ((|v_seq_26| > 0)) then (v_seq_26[v_int_71]) else ((if ((|v_seq_28| > 0)) then (v_seq_28[v_int_73]) else (('m' == 'h'))))) {
			return ;
		}
		var v_seq_29: seq<char> := [];
		var v_seq_30: seq<char> := v_seq_29;
		var v_int_74: int := 29;
		var v_int_75: int := safe_index_seq(v_seq_30, v_int_74);
		var v_int_76: int := v_int_75;
		var v_seq_31: seq<char> := ['H', 'C', 'F'];
		var v_seq_32: seq<char> := v_seq_31;
		var v_int_77: int := 10;
		var v_int_78: int := safe_index_seq(v_seq_32, v_int_77);
		var v_int_79: int := v_int_78;
		var v_seq_34: seq<char> := ((if ((|v_seq_29| > 0)) then (v_seq_29[v_int_76 := 'U']) else (v_seq_29)) + (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_79 := 'C']) else (v_seq_31)));
		var v_seq_33: seq<int> := ([20, 24, 29, 8] + [19, 22, 0]);
		var v_int_80: int := (if (false) then (-7) else (9));
		var v_map_19: map<char, int> := map['l' := 4, 'X' := 19, 'M' := 26];
		var v_char_14: char := 'S';
		var v_int_81: int := (if ((|v_seq_33| > 0)) then (v_seq_33[v_int_80]) else ((if ((v_char_14 in v_map_19)) then (v_map_19[v_char_14]) else (-13))));
		v_char_5 := (if ((|v_seq_34| > 0)) then (v_seq_34[v_int_81]) else (v_char_5));
		assert true;
		expect true;
		assert true;
		expect true;
		var v_int_82: int := v_int_76;
		var v_map_21: map<char, set<char>> := (if (true) then (map['R' := {'o', 'o', 'N'}]) else (map['d' := {'Q', 'H', 'G', 'g'}, 'U' := {'B'}, 'n' := {'M', 'd', 'V', 'v'}, 'Q' := {}, 'A' := {'a', 'F', 'L'}]));
		var v_char_16: char := v_char_5;
		var v_map_20: map<char, set<char>> := map['k' := {'a', 'm'}, 'U' := {}];
		var v_char_15: char := 'g';
		var v_int_83: int := |(if ((v_char_16 in v_map_21)) then (v_map_21[v_char_16]) else ((if ((v_char_15 in v_map_20)) then (v_map_20[v_char_15]) else ({'I', 'V'}))))|;
		while (v_int_82 < v_int_83) 
			decreases v_int_83 - v_int_82;
			invariant (v_int_82 <= v_int_83);
		{
			v_int_82 := (v_int_82 + 1);
			var v_seq_35: seq<bool> := [];
			var v_int_85: int := 20;
			var v_seq_36: seq<bool> := [true, true, true];
			var v_int_86: int := 15;
			var v_map_22: map<char, int> := map['t' := 9, 'y' := 16, 'g' := 4, 'o' := 7, 'v' := 28]['F' := 21];
			var v_char_17: char := v_char_16;
			var v_map_23: map<char, int> := map['f' := 17, 'f' := 8, 'v' := 12, 'P' := -5];
			var v_char_18: char := 'w';
			var v_map_24: map<char, int> := map['V' := 6, 'j' := 2];
			var v_char_19: char := 'b';
			var v_int_99: int, v_int_100: int := (if ((if ((if ((|v_seq_35| > 0)) then (v_seq_35[v_int_85]) else (true))) then (v_bool_2) else ((if ((|v_seq_36| > 0)) then (v_seq_36[v_int_86]) else (false))))) then ((match 't' {
				case _ => (if (true) then (14) else (0))
			})) else ((if ((v_char_17 in v_map_22)) then (v_map_22[v_char_17]) else ((22 + 2))))), (v_int_int_2.1 - (match 'Y' {
				case _ => (if ((v_char_19 in v_map_24)) then (v_map_24[v_char_19]) else (18))
			}));
			for v_int_84 := v_int_99 to v_int_100 
				invariant (v_int_100 - v_int_84 >= 0)
			{
				var v_map_26: map<char, char> := (match 'g' {
					case _ => map['l' := 'G']['e' := 'O']
				});
				var v_char_21: char := v_array_3[2];
				var v_seq_37: seq<map<char, char>> := [map['v' := 't'], map['s' := 'e'], map['F' := 'N', 'j' := 'G', 'i' := 'Y', 'w' := 'c'], map['s' := 'Y', 'A' := 'v', 'z' := 'N']];
				var v_int_87: int := 5;
				var v_map_25: map<char, char> := (if ((|v_seq_37| > 0)) then (v_seq_37[v_int_87]) else (map['x' := 'K']));
				var v_seq_38: seq<char> := ['J', 'N', 'f'];
				var v_int_88: int := 21;
				var v_char_20: char := (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_88]) else ('D'));
				var v_seq_39: seq<char> := (if (true) then (['V', 'Y', 'L']) else ([]));
				var v_int_89: int := (match 'k' {
					case _ => 19
				});
				var v_seq_40: seq<char> := ['w', 'd', 'f', 'C'];
				var v_seq_41: seq<char> := v_seq_40;
				var v_int_90: int := 25;
				var v_int_91: int := safe_index_seq(v_seq_41, v_int_90);
				var v_int_92: int := v_int_91;
				var v_seq_42: seq<char> := (if ((|v_seq_40| > 0)) then (v_seq_40[v_int_92 := 'R']) else (v_seq_40));
				var v_int_93: int := (-14 - 7);
				var v_seq_43: seq<char> := (match 'D' {
					case _ => ['z', 'R', 'g']
				});
				var v_seq_44: seq<char> := v_seq_43;
				var v_int_94: int := (match 'R' {
					case _ => 26
				});
				var v_int_95: int := safe_index_seq(v_seq_44, v_int_94);
				var v_int_96: int := v_int_95;
				var v_map_27: map<char, char> := map['h' := 'C', 'z' := 'C'];
				var v_char_22: char := 'k';
				var v_seq_45: seq<char> := (if ((|v_seq_43| > 0)) then (v_seq_43[v_int_96 := (if ((v_char_22 in v_map_27)) then (v_map_27[v_char_22]) else ('f'))]) else (v_seq_43));
				var v_int_97: int := v_int_62;
				var v_seq_46: seq<char> := (if (false) then (['q', 'o', 'h']) else (['Y']));
				var v_seq_47: seq<char> := (if ((|v_seq_46| > 0)) then (v_seq_46[(29.36).Floor..(match 'N' {
					case _ => 23
				})]) else (v_seq_46));
				var v_int_98: int := v_int_82;
				var v_map_28: map<char, char> := map['R' := 'D'];
				var v_char_23: char := 'l';
				v_array_3[0], v_char_14, v_char_15, v_char_22, v_char_20 := (if ((v_char_21 in v_map_26)) then (v_map_26[v_char_21]) else ((if ((v_char_20 in v_map_25)) then (v_map_25[v_char_20]) else ((if (false) then ('R') else ('Y')))))), (if ((v_bool_3 <== (if (true) then (true) else (false)))) then ((if ((|v_seq_39| > 0)) then (v_seq_39[v_int_89]) else ((if (true) then ('h') else ('N'))))) else ((if ((|v_seq_42| > 0)) then (v_seq_42[v_int_93]) else ((if (false) then ('G') else ('y')))))), (if ((|v_seq_45| > 0)) then (v_seq_45[v_int_97]) else ((if (({'Z'} !! {})) then (v_char_20) else ((if (true) then ('j') else ('z')))))), (if ((|v_seq_47| > 0)) then (v_seq_47[v_int_98]) else ((if ((match 'n' {
					case _ => false
				})) then ((match 'i' {
					case _ => 'V'
				})) else ((if ((v_char_23 in v_map_28)) then (v_map_28[v_char_23]) else ('D')))))), v_char_21;
				assert true;
				expect true;
				return ;
			}
			v_char_6 := (match 'N' {
				case _ => v_array_3[1]
			});
			return ;
		}
		var v_map_29: map<char, bool> := map['N' := true, 'R' := true, 'B' := false, 'C' := false, 'G' := false];
		var v_char_24: char := 'n';
		var v_seq_48: seq<char> := [];
		var v_int_101: int := 20;
		var v_map_30: map<char, char> := map['J' := 'Z'];
		var v_char_25: char := 'g';
		var v_map_31: map<char, char> := map['Z' := 'j', 'Q' := 'I', 'C' := 'K']['J' := 'y'];
		var v_char_26: char := (match 'n' {
			case _ => 'f'
		});
		var v_seq_49: seq<char> := ['w'];
		var v_int_102: int := 20;
		var v_seq_50: seq<char> := ['c'];
		var v_seq_51: seq<char> := (if ((|v_seq_50| > 0)) then (v_seq_50[14..0]) else (v_seq_50));
		var v_seq_52: seq<char> := v_seq_51;
		var v_int_103: int := (7 + -19);
		var v_int_104: int := safe_index_seq(v_seq_52, v_int_103);
		var v_int_105: int := v_int_104;
		var v_map_32: map<char, char> := map['m' := 'h', 'h' := 'T', 'v' := 'E', 'K' := 'f'];
		var v_char_27: char := 'f';
		var v_seq_54: seq<char> := (if ((|v_seq_51| > 0)) then (v_seq_51[v_int_105 := (if ((v_char_27 in v_map_32)) then (v_map_32[v_char_27]) else ('l'))]) else (v_seq_51));
		var v_map_34: map<char, int> := (if (true) then (map['C' := 0, 'g' := 19, 'v' := -19, 'E' := 3, 'C' := 2]) else (map['z' := 27, 'u' := 2, 'r' := 14]));
		var v_seq_53: seq<char> := ['z', 'O'];
		var v_int_106: int := 19;
		var v_char_29: char := (if ((|v_seq_53| > 0)) then (v_seq_53[v_int_106]) else ('U'));
		var v_map_33: map<char, int> := map['W' := 23, 'O' := 18, 'A' := 3, 'Q' := 22];
		var v_char_28: char := 'F';
		var v_int_107: int := (if ((v_char_29 in v_map_34)) then (v_map_34[v_char_29]) else ((if ((v_char_28 in v_map_33)) then (v_map_33[v_char_28]) else (16))));
		var v_seq_55: seq<char> := v_seq_54;
		var v_int_108: int := (8 % 13);
		var v_map_35: map<char, char> := map['Y' := 'x', 'c' := 'a', 's' := 'E', 'i' := 'k'];
		var v_char_30: char := 'N';
		v_char_27, v_char_30, v_array_3[2] := (if ((v_char_6 !in v_seq_29)) then ((if ((if ((v_char_24 in v_map_29)) then (v_map_29[v_char_24]) else (false))) then ((if ((|v_seq_48| > 0)) then (v_seq_48[v_int_101]) else ('M'))) else (v_char_15))) else ((match 'h' {
			case _ => (match 'W' {
				case _ => 'T'
			})
		}))), (if (v_bool_2) then ((if ((v_char_26 in v_map_31)) then (v_map_31[v_char_26]) else (v_char_16))) else ((match 'k' {
			case _ => v_char_16
		}))), (if ((|v_seq_54| > 0)) then (v_seq_54[v_int_107]) else ((if ((|v_seq_55| > 0)) then (v_seq_55[v_int_108]) else ((if ((v_char_30 in v_map_35)) then (v_map_35[v_char_30]) else ('n'))))));
		var v_map_36: map<char, map<char, bool>> := map['T' := map['T' := false, 'O' := true], 't' := map['L' := true, 'a' := true, 'g' := false, 'U' := false], 'i' := map['V' := true, 'h' := false, 'R' := false, 'B' := true, 'J' := true], 'U' := map['J' := true, 'V' := false, 'U' := true]]['P' := map['N' := true, 'o' := false, 'R' := true, 'r' := true, 'h' := true]];
		var v_char_31: char := (match 'e' {
			case _ => 'T'
		});
		var v_map_37: map<char, bool> := (if ((v_char_31 in v_map_36)) then (v_map_36[v_char_31]) else (map['B' := false, 'P' := false, 'G' := true, 'Q' := true, 'E' := false]['Q' := true]));
		var v_char_32: char := v_char_27;
		var v_seq_56: seq<bool> := [false, true];
		var v_int_109: int := 26;
		if (if ((v_char_32 in v_map_37)) then (v_map_37[v_char_32]) else ((match 'X' {
			case _ => (if ((|v_seq_56| > 0)) then (v_seq_56[v_int_109]) else (false))
		}))) {
			var v_map_39: map<char, char> := map['h' := 'd', 'g' := 'x']['B' := 'p'];
			var v_map_38: map<char, char> := map['J' := 'd', 's' := 'J', 'B' := 'E'];
			var v_char_33: char := 'P';
			var v_char_34: char := (if ((v_char_33 in v_map_38)) then (v_map_38[v_char_33]) else ('f'));
			var v_seq_57: seq<char> := ['Q', 'm', 'f'];
			var v_int_110: int := 21;
			var v_map_40: map<char, char> := map['W' := 'w']['O' := 'G'];
			var v_char_35: char := v_char_32;
			v_char_6, v_char_3 := v_char_24, (match 'g' {
				case _ => (if ((v_char_35 in v_map_40)) then (v_map_40[v_char_35]) else (v_char_14))
			});
			var v_seq_58: seq<char> := ['j'];
			var v_seq_59: seq<char> := ['X', 'X', 'K'];
			var v_seq_60: seq<char> := v_seq_59;
			var v_int_111: int := 26;
			var v_int_112: int := safe_index_seq(v_seq_60, v_int_111);
			var v_int_113: int := v_int_112;
			var v_seq_61: seq<char> := ((if ((|v_seq_58| > 0)) then (v_seq_58[15..15]) else (v_seq_58)) + (if ((|v_seq_59| > 0)) then (v_seq_59[v_int_113 := 'H']) else (v_seq_59)));
			var v_int_114: int := (match 'b' {
				case _ => v_int_53
			});
			var v_map_41: map<char, bool> := map['w' := false, 'T' := true, 'I' := true, 't' := false];
			var v_char_36: char := 'Y';
			var v_map_42: map<char, char> := map['k' := 'p', 'Z' := 'H', 'h' := 'L', 'g' := 'g', 'R' := 'e'];
			var v_char_37: char := 'u';
			v_char_14 := (if ((|v_seq_61| > 0)) then (v_seq_61[v_int_114]) else ((if ((if ((v_char_36 in v_map_41)) then (v_map_41[v_char_36]) else (false))) then ((match 'L' {
				case _ => 'X'
			})) else ((if ((v_char_37 in v_map_42)) then (v_map_42[v_char_37]) else ('f'))))));
			assert true;
			expect true;
			return ;
		}
		var v_seq_62: seq<seq<char>> := [];
		var v_seq_63: seq<seq<char>> := (if ((|v_seq_62| > 0)) then (v_seq_62[13..-5]) else (v_seq_62));
		var v_int_115: int := (match 'u' {
			case _ => 26
		});
		var v_seq_64: seq<char> := ['q', 'u', 'T', 'z'];
		var v_seq_65: seq<char> := v_seq_64;
		var v_int_116: int := 20;
		var v_int_117: int := safe_index_seq(v_seq_65, v_int_116);
		var v_int_118: int := v_int_117;
		var v_seq_66: seq<char> := (if ((|v_seq_63| > 0)) then (v_seq_63[v_int_115]) else ((if ((|v_seq_64| > 0)) then (v_seq_64[v_int_118 := 'k']) else (v_seq_64))));
		var v_int_119: int := v_int_int_3.0;
		var v_map_43: map<char, map<char, char>> := map['a' := map['h' := 'b', 'K' := 'E', 'G' := 'l', 'G' := 'v'], 'Z' := map['s' := 'B'], 'r' := map['R' := 'x', 'a' := 'p'], 'B' := map['E' := 'O', 'O' := 'k', 'a' := 'K', 'k' := 'W'], 'y' := map['A' := 'z', 'Q' := 'V', 'B' := 'T', 'p' := 'a', 'Z' := 'P']];
		var v_char_38: char := 'Q';
		var v_map_44: map<char, char> := (if ((v_char_38 in v_map_43)) then (v_map_43[v_char_38]) else (map['Z' := 'Y', 'c' := 'm', 'L' := 'J', 'y' := 'S', 'w' := 'l']));
		var v_char_39: char := v_array_3[0];
		v_char_6 := (if ((|v_seq_66| > 0)) then (v_seq_66[v_int_119]) else ((if ((v_char_39 in v_map_44)) then (v_map_44[v_char_39]) else ((match 'j' {
			case _ => 'c'
		})))));
		var v_map_45: map<char, seq<map<char, char>>> := map['B' := [map['J' := 'w', 'W' := 'C'], map['q' := 'X', 'a' := 'B', 'c' := 'p']]];
		var v_char_40: char := 'C';
		var v_seq_67: seq<map<char, char>> := (if ((v_char_40 in v_map_45)) then (v_map_45[v_char_40]) else ([map['k' := 'L', 'l' := 'k', 'O' := 'k'], map['f' := 'q']]));
		var v_map_46: map<char, int> := map['g' := 14];
		var v_char_41: char := 'h';
		var v_int_122: int := (if ((v_char_41 in v_map_46)) then (v_map_46[v_char_41]) else (9));
		var v_int_120: int := |(if ((|v_seq_67| > 0)) then (v_seq_67[v_int_122]) else (map['p' := 'n', 'm' := 'C', 'C' := 'X', 'r' := 't', 'w' := 'P']['e' := 'w']))|;
		var v_seq_68: seq<int> := ([21] + [28, 13, 22, -16]);
		var v_map_47: map<char, int> := map['s' := 28, 'i' := 28];
		var v_char_42: char := 'B';
		var v_seq_69: seq<int> := (if ((|v_seq_68| > 0)) then (v_seq_68[(if ((v_char_42 in v_map_47)) then (v_map_47[v_char_42]) else (15))..(if (false) then (15) else (16))]) else (v_seq_68));
		var v_int_123: int := (match 'E' {
			case _ => (if (true) then (19) else (4))
		});
		var v_int_121: int := (if ((|v_seq_69| > 0)) then (v_seq_69[v_int_123]) else (v_int_119));
		while (v_int_120 < v_int_121) 
			decreases v_int_121 - v_int_120;
			invariant (v_int_120 <= v_int_121);
		{
			v_int_120 := (v_int_120 + 1);
			return ;
		}
		var v_map_49: map<char, bool> := (if (false) then (map['d' := true, 'm' := false, 'q' := false, 'g' := true, 'b' := false]) else (map['T' := true, 's' := true, 'v' := true, 'S' := true, 'z' := false]));
		var v_map_48: map<char, char> := map['e' := 'X', 'R' := 'm', 't' := 'a', 'T' := 'F'];
		var v_char_43: char := 'G';
		var v_char_44: char := (if ((v_char_43 in v_map_48)) then (v_map_48[v_char_43]) else ('S'));
		var v_seq_70: seq<bool> := [];
		var v_int_124: int := 18;
		var v_seq_71: seq<char> := ['m', 'r'];
		var v_int_125: int := 10;
		match (if ((if ((v_char_44 in v_map_49)) then (v_map_49[v_char_44]) else ((match 'M' {
			case _ => true
		})))) then ((if ((if ((|v_seq_70| > 0)) then (v_seq_70[v_int_124]) else (true))) then (v_char_24) else ((if ((|v_seq_71| > 0)) then (v_seq_71[v_int_125]) else ('Z'))))) else (v_array_3[2])) {
			case _ => {
				assert true;
				expect true;
			}
			
		}
		
	}
}

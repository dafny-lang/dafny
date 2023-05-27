// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1> = DT_1_1 | DT_1_4(DT_1_4_1: T_1, DT_1_4_2: T_1)
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

method m_method_6(p_m_method_6_1: char) returns (ret_1: array<int>)
	requires ((p_m_method_6_1 == 'Y'));
	ensures (((p_m_method_6_1 == 'Y')) ==> (ret_1.Length == 4 && (ret_1[0] == 25) && (ret_1[1] == 21) && (ret_1[2] == 29) && (ret_1[3] == 8)));
{
	var v_seq_15: seq<int> := [24, 18];
	var v_int_59: int := 27;
	var v_seq_21: seq<int> := v_seq_15;
	var v_int_87: int := v_int_59;
	var v_int_88: int := safe_index_seq(v_seq_21, v_int_87);
	v_int_59 := v_int_88;
	match (if ((|v_seq_15| > 0)) then (v_seq_15[v_int_59]) else (29)) {
		case 7 => {
			if (multiset({10, 29, 10}) != multiset({3, -16, 9})) {
				var v_array_2: array<int> := new int[3] [10, 21, 13];
				var v_array_3: array<int> := new int[5] [-27, 11, 5, 7, 5];
				return (if (false) then (v_array_2) else (v_array_3));
			}
			var v_map_8: map<int, int> := map[29 := 4, 13 := 11, 15 := 9, 27 := 3];
			var v_int_60: int := 9;
			var v_map_9: map<int, real> := map[4 := -21.69];
			var v_int_61: int := 15;
			var v_int_62: int, v_int_63: int, v_int_64: int, v_real_2: real, v_int_65: int := |{16, 11, 16, 26}|, (if ((v_int_60 in v_map_8)) then (v_map_8[v_int_60]) else (3)), (14 / 6), (if ((v_int_61 in v_map_9)) then (v_map_9[v_int_61]) else (22.14)), v_int_59;
			assert true;
			expect true;
			if ([] == [17]) {
				
			} else {
				var v_array_4: array<int> := new int[5] [19, 19, 21, 21, 2];
				var v_array_5: array<int> := new int[5] [4, 20, 26, 20, 25];
				var v_array_6: array<int> := new int[4];
				v_array_6[0] := -16;
				v_array_6[1] := 8;
				v_array_6[2] := 15;
				v_array_6[3] := 12;
				var v_map_10: map<int, array<int>> := map[11 := v_array_4, 14 := v_array_5, 24 := v_array_6];
				var v_int_66: int := -8;
				var v_array_7: array<int> := new int[3] [11, -25, 19];
				return (if ((v_int_66 in v_map_10)) then (v_map_10[v_int_66]) else (v_array_7));
			}
			if (multiset{11} >= multiset{13}) {
				var v_array_8: array<int> := new int[5] [25, 27, 14, 27, 5];
				var v_array_9: array<int> := new int[3] [25, 6, 9];
				var v_map_11: map<int, array<int>> := map[8 := v_array_8, 18 := v_array_9];
				var v_int_67: int := 20;
				var v_array_10: array<int> := new int[4] [19, 8, 11, 4];
				return (if ((v_int_67 in v_map_11)) then (v_map_11[v_int_67]) else (v_array_10));
			}
			var v_int_69: int, v_int_70: int := (match 13 {
				case _ => 26
			}), (6 * 21);
			for v_int_68 := v_int_69 to v_int_70 
				invariant (v_int_70 - v_int_68 >= 0)
			{
				
			}
			var v_array_11: array<int> := new int[4] [22, 23, 1, 17];
			var v_map_12: map<int, array<int>> := map[28 := v_array_11];
			var v_int_71: int := 12;
			var v_array_12: array<int> := new int[3] [14, 6, 21];
			return (if ((v_int_71 in v_map_12)) then (v_map_12[v_int_71]) else (v_array_12));
		}
			case _ => {
			var v_bool_int_bool_1: (bool, int, bool) := (false, -15, false);
			var v_array_13: array<bool> := new bool[4] [true, true, false, true];
			var v_bool_int_bool_array_1: ((bool, int, bool), array<bool>) := (v_bool_int_bool_1, v_array_13);
			var v_seq_16: seq<((bool, int, bool), array<bool>)> := [v_bool_int_bool_array_1];
			var v_int_72: int := 12;
			var v_seq_22: seq<((bool, int, bool), array<bool>)> := v_seq_16;
			var v_int_89: int := v_int_72;
			var v_int_90: int := safe_index_seq(v_seq_22, v_int_89);
			v_int_72 := v_int_90;
			var v_bool_int_bool_2: (bool, int, bool) := (false, -28, false);
			var v_array_14: array<bool> := new bool[5] [true, false, true, true, true];
			var v_bool_int_bool_array_2: ((bool, int, bool), array<bool>) := (v_bool_int_bool_2, v_array_14);
			var v_bool_2: bool, v_bool_int_bool_array_3: ((bool, int, bool), array<bool>), v_char_2: char := (match 25 {
				case 18 => false
				case _ => false
			}), (if ((|v_seq_16| > 0)) then (v_seq_16[v_int_72]) else (v_bool_int_bool_array_2)), (if (true) then ('M') else ('v'));
			var v_bool_int_bool_3: (bool, int, bool) := (false, -15, false);
			var v_bool_int_bool_array_4: ((bool, int, bool), array<bool>) := (v_bool_int_bool_3, v_array_13);
			var v_bool_int_bool_4: (bool, int, bool) := (false, -28, false);
			var v_bool_int_bool_array_5: ((bool, int, bool), array<bool>) := (v_bool_int_bool_4, v_array_14);
			var v_bool_int_bool_5: (bool, int, bool) := (false, -15, false);
			var v_bool_int_bool_array_6: ((bool, int, bool), array<bool>) := (v_bool_int_bool_5, v_array_13);
			var v_bool_int_bool_6: (bool, int, bool) := (false, -15, false);
			var v_bool_int_bool_array_7: ((bool, int, bool), array<bool>) := (v_bool_int_bool_6, v_array_13);
			print "v_array_14[3]", " ", v_array_14[3], " ", "v_bool_2", " ", v_bool_2, " ", "v_array_13[0]", " ", v_array_13[0], " ", "v_array_13[2]", " ", v_array_13[2], " ", "v_array_14[1]", " ", v_array_14[1], " ", "v_seq_16", " ", (v_seq_16 == [v_bool_int_bool_array_4]), " ", "v_bool_int_bool_2", " ", v_bool_int_bool_2, " ", "v_bool_int_bool_1", " ", v_bool_int_bool_1, " ", "v_array_14", " ", (v_array_14 == v_array_14), " ", "v_array_13", " ", (v_array_13 == v_array_13), " ", "v_array_14[4]", " ", v_array_14[4], " ", "v_bool_int_bool_array_2", " ", (v_bool_int_bool_array_2 == v_bool_int_bool_array_5), " ", "v_bool_int_bool_array_1", " ", (v_bool_int_bool_array_1 == v_bool_int_bool_array_6), " ", "v_char_2", " ", (v_char_2 == 'M'), " ", "v_array_13[1]", " ", v_array_13[1], " ", "v_array_14[0]", " ", v_array_14[0], " ", "v_bool_int_bool_array_3", " ", (v_bool_int_bool_array_3 == v_bool_int_bool_array_7), " ", "v_array_13[3]", " ", v_array_13[3], " ", "v_array_14[2]", " ", v_array_14[2], " ", "v_bool_int_bool_1.0", " ", v_bool_int_bool_1.0, " ", "v_bool_int_bool_1.1", " ", v_bool_int_bool_1.1, " ", "v_bool_int_bool_2.0", " ", v_bool_int_bool_2.0, " ", "v_bool_int_bool_array_2.1", " ", (v_bool_int_bool_array_2.1 == v_array_14), " ", "v_bool_int_bool_1.2", " ", v_bool_int_bool_1.2, " ", "v_bool_int_bool_array_1.1", " ", (v_bool_int_bool_array_1.1 == v_array_13), " ", "v_bool_int_bool_2.1", " ", v_bool_int_bool_2.1, " ", "v_bool_int_bool_array_2.0", " ", v_bool_int_bool_array_2.0, " ", "v_bool_int_bool_array_1.0", " ", v_bool_int_bool_array_1.0, " ", "v_int_72", " ", v_int_72, " ", "v_bool_int_bool_2.2", " ", v_bool_int_bool_2.2, " ", "v_seq_15", " ", v_seq_15, " ", "v_int_59", " ", v_int_59, " ", "p_m_method_6_1", " ", (p_m_method_6_1 == 'Y'), "\n";
		}
		
	}
	
	var v_array_15: array<int> := new int[5] [13, 16, -18, 2, -3];
	var v_array_16: array<int> := new int[4];
	v_array_16[0] := 25;
	v_array_16[1] := 21;
	v_array_16[2] := 29;
	v_array_16[3] := 8;
	var v_array_17: array<int> := new int[4] [7, 13, 27, 26];
	var v_seq_17: seq<array<int>> := [v_array_15, v_array_16, v_array_17];
	var v_int_73: int := 1;
	var v_array_18: array<int> := new int[5] [-22, 10, 12, 7, 12];
	print "v_array_15[2]", " ", v_array_15[2], " ", "v_array_16[1]", " ", v_array_16[1], " ", "v_array_15[4]", " ", v_array_15[4], " ", "v_array_16[3]", " ", v_array_16[3], " ", "v_array_17[2]", " ", v_array_17[2], " ", "v_array_18[1]", " ", v_array_18[1], " ", "v_array_15[0]", " ", v_array_15[0], " ", "v_array_17[0]", " ", v_array_17[0], " ", "v_seq_15", " ", v_seq_15, " ", "v_seq_17", " ", (v_seq_17 == [v_array_15, v_array_16, v_array_17]), " ", "v_array_18", " ", (v_array_18 == v_array_18), " ", "v_array_17", " ", (v_array_17 == v_array_17), " ", "v_array_16", " ", (v_array_16 == v_array_16), " ", "v_array_18[3]", " ", v_array_18[3], " ", "v_array_15", " ", (v_array_15 == v_array_15), " ", "p_m_method_6_1", " ", (p_m_method_6_1 == 'Y'), " ", "v_array_15[3]", " ", v_array_15[3], " ", "v_array_16[2]", " ", v_array_16[2], " ", "v_array_17[3]", " ", v_array_17[3], " ", "v_array_18[2]", " ", v_array_18[2], " ", "v_array_17[1]", " ", v_array_17[1], " ", "v_array_18[0]", " ", v_array_18[0], " ", "v_array_15[1]", " ", v_array_15[1], " ", "v_array_16[0]", " ", v_array_16[0], " ", "v_int_59", " ", v_int_59, " ", "v_array_18[4]", " ", v_array_18[4], " ", "v_int_73", " ", v_int_73, "\n";
	return (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_73]) else (v_array_18));
}

method m_method_5(p_m_method_5_1: int, p_m_method_5_2: int, p_m_method_5_3: int, p_m_method_5_4: int) returns (ret_1: seq<int>)
	requires ((p_m_method_5_4 == 0) && (p_m_method_5_1 == -3) && (p_m_method_5_3 == -4) && (p_m_method_5_2 == 17));
	ensures (((p_m_method_5_4 == 0) && (p_m_method_5_1 == -3) && (p_m_method_5_3 == -4) && (p_m_method_5_2 == 17)) ==> (|ret_1| == 2 && (ret_1[0] == 22) && (ret_1[1] == 26)));
{
	assert ((p_m_method_5_4 == 0) && (p_m_method_5_2 == 17) && (p_m_method_5_1 == -3));
	expect ((p_m_method_5_4 == 0) && (p_m_method_5_2 == 17) && (p_m_method_5_1 == -3));
	assert ((p_m_method_5_1 == -3) && (p_m_method_5_3 == -4) && (p_m_method_5_4 == 0));
	expect ((p_m_method_5_1 == -3) && (p_m_method_5_3 == -4) && (p_m_method_5_4 == 0));
	var v_seq_11: seq<seq<int>> := [[22, 26], [14], [], []];
	var v_int_48: int := 19;
	var v_seq_20: seq<seq<int>> := v_seq_11;
	var v_int_85: int := v_int_48;
	var v_int_86: int := safe_index_seq(v_seq_20, v_int_85);
	v_int_48 := v_int_86;
	print "v_seq_11", " ", v_seq_11, " ", "v_int_48", " ", v_int_48, " ", "p_m_method_5_4", " ", p_m_method_5_4, " ", "p_m_method_5_3", " ", p_m_method_5_3, " ", "p_m_method_5_2", " ", p_m_method_5_2, " ", "p_m_method_5_1", " ", p_m_method_5_1, "\n";
	return (if ((|v_seq_11| > 0)) then (v_seq_11[v_int_48]) else ([25]));
}

method m_method_4(p_m_method_4_1: int, p_m_method_4_2: int, p_m_method_4_3: int) returns (ret_1: bool)
	requires ((p_m_method_4_2 == 5) && (p_m_method_4_1 == 0) && (p_m_method_4_3 == 13));
	ensures (((p_m_method_4_2 == 5) && (p_m_method_4_1 == 0) && (p_m_method_4_3 == 13)) ==> ((ret_1 == true)));
{
	print "p_m_method_4_1", " ", p_m_method_4_1, " ", "p_m_method_4_3", " ", p_m_method_4_3, " ", "p_m_method_4_2", " ", p_m_method_4_2, "\n";
	return true;
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: int, p_m_method_3_3: int, p_m_method_3_4: char) returns (ret_1: real)
	requires ((p_m_method_3_1 == 4) && (p_m_method_3_3 == 16) && (p_m_method_3_2 == 5) && (p_m_method_3_4 == 'Y'));
	ensures (((p_m_method_3_1 == 4) && (p_m_method_3_3 == 16) && (p_m_method_3_2 == 5) && (p_m_method_3_4 == 'Y')) ==> ((1.17 < ret_1 < 1.37)));
{
	print "p_m_method_3_2", " ", p_m_method_3_2, " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_4", " ", (p_m_method_3_4 == 'Y'), " ", "p_m_method_3_3", " ", p_m_method_3_3, "\n";
	return 1.27;
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

method m_method_2(p_m_method_2_1: int) returns (ret_1: map<int, int>)
	requires ((p_m_method_2_1 == 16));
	ensures (((p_m_method_2_1 == 16)) ==> ((ret_1 == map[0 := 18])));
{
	var v_int_18: int, v_int_19: int := 18, 12;
	for v_int_15 := v_int_18 downto v_int_19 
		invariant (v_int_15 - v_int_19 >= 0)
	{
		var v_int_16: int := 22;
		var v_int_17: int := 11;
		while (v_int_16 < v_int_17) 
			decreases v_int_17 - v_int_16;
			invariant (v_int_16 <= v_int_17);
		{
			v_int_16 := (v_int_16 + 1);
			return map[15 := 29, 3 := -17, -3 := 28, 8 := 20];
		}
		match 17 {
			case 1 => {
				return map[29 := 19, 24 := 5, 11 := 9, 19 := 0];
			}
				case 5 => {
				return map[6 := 21, 4 := 18, -3 := 14, 13 := 12];
			}
				case _ => {
				print "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "p_m_method_2_1", " ", p_m_method_2_1, "\n";
				return map[0 := 18];
			}
			
		}
		
	}
	return map[-18 := 9];
}

method m_method_1(p_m_method_1_1: int, p_m_method_1_2: int, p_m_method_1_3: int, p_m_method_1_4: int) returns (ret_1: int, ret_2: int, ret_3: int, ret_4: int)
	requires ((p_m_method_1_1 == 0) && (p_m_method_1_3 == 1) && (p_m_method_1_2 == 1) && (p_m_method_1_4 == 0));
	ensures (((p_m_method_1_1 == 0) && (p_m_method_1_3 == 1) && (p_m_method_1_2 == 1) && (p_m_method_1_4 == 0)) ==> ((ret_1 == 0) && (ret_2 == 17) && (ret_3 == 26) && (ret_4 == -3)));
{
	assert ((p_m_method_1_4 == 0) && (p_m_method_1_2 == 1));
	expect ((p_m_method_1_4 == 0) && (p_m_method_1_2 == 1));
	assert ((p_m_method_1_4 == 0) && (p_m_method_1_1 == 0));
	expect ((p_m_method_1_4 == 0) && (p_m_method_1_1 == 0));
	var v_map_2: map<int, int> := (map[0 := 17, 22 := 12, 8 := 26] + (map[9 := 26] + map[5 := 25, 28 := -11, 7 := 5, 6 := -9]));
	var v_int_8: int := p_m_method_1_4;
	var v_map_1: map<int, int> := map[26 := 1, 12 := 15, 17 := 8];
	var v_int_7: int := 16;
	var v_int_9: int := (if ((v_int_7 in v_map_1)) then (v_map_1[v_int_7]) else (26));
	var v_int_10: int := safe_division(v_int_8, v_int_9);
	var v_int_11: int := v_int_10;
	var v_map_4: map<int, map<int, int>> := map[5 := map[1 := 4, 12 := 9], 17 := map[-9 := 2, 2 := 7, -3 := 9]][18 := map[22 := 6, 24 := 7, 18 := -22, 28 := -27]];
	var v_int_12: int := -22;
	var v_int_13: int := 8;
	var v_int_14: int := safe_division(v_int_12, v_int_13);
	var v_int_21: int := v_int_14;
	var v_int_20: int := 16;
	var v_map_3: map<int, int> := m_method_2(v_int_20);
	var v_map_5: map<int, int> := (if ((v_int_21 in v_map_4)) then (v_map_4[v_int_21]) else (v_map_3));
	var v_int_22: int := v_int_21;
	var v_map_6: map<int, int> := v_map_1;
	var v_seq_3: seq<int> := [5, 15, 10];
	var v_seq_18: seq<int> := v_seq_3;
	var v_int_76: int := -2;
	var v_int_77: int := 8;
	var v_int_78: int, v_int_79: int := safe_subsequence(v_seq_18, v_int_76, v_int_77);
	var v_int_74: int, v_int_75: int := v_int_78, v_int_79;
	var v_seq_4: seq<int> := (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_74..v_int_75]) else (v_seq_3));
	var v_int_23: int := v_int_14;
	var v_int_80: int := 9;
	var v_int_81: int := 0;
	var v_int_82: int := safe_division(v_int_80, v_int_81);
	var v_int_24: int := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_23]) else (v_int_82));
	print "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "p_m_method_1_2", " ", p_m_method_1_2, " ", "v_int_22", " ", v_int_22, " ", "p_m_method_1_1", " ", p_m_method_1_1, " ", "v_int_21", " ", v_int_21, " ", "v_int_9", " ", v_int_9, " ", "p_m_method_1_4", " ", p_m_method_1_4, " ", "v_int_20", " ", v_int_20, " ", "p_m_method_1_3", " ", p_m_method_1_3, " ", "v_map_5", " ", (v_map_5 == map[0 := 18]), " ", "v_map_4", " ", (v_map_4 == map[17 := map[2 := 7, -3 := 9, -9 := 2], 18 := map[18 := -22, 22 := 6, 24 := 7, 28 := -27], 5 := map[1 := 4, 12 := 9]]), " ", "v_map_6", " ", (v_map_6 == map[17 := 8, 26 := 1, 12 := 15]), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_map_1", " ", (v_map_1 == map[17 := 8, 26 := 1, 12 := 15]), " ", "v_map_3", " ", (v_map_3 == map[0 := 18]), " ", "v_map_2", " ", (v_map_2 == map[0 := 17, 5 := 25, 22 := 12, 6 := -9, 7 := 5, 8 := 26, 9 := 26, 28 := -11]), " ", "v_int_13", " ", v_int_13, " ", "v_int_12", " ", v_int_12, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_seq_4", " ", v_seq_4, " ", "v_seq_3", " ", v_seq_3, " ", "v_int_14", " ", v_int_14, "\n";
	return p_m_method_1_1, (if ((v_int_11 in v_map_2)) then (v_map_2[v_int_11]) else (24)), (if ((v_int_22 in v_map_5)) then (v_map_5[v_int_22]) else (v_int_9)), (if ((v_int_24 in v_map_6)) then (v_map_6[v_int_24]) else (v_int_21));
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_seq_5: seq<seq<int>> := [];
	var v_int_25: int := 25;
	var v_seq_6: seq<int> := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_25]) else ([3, 8, 5]));
	var v_seq_7: seq<int> := v_seq_6;
	var v_int_26: int := (match 16 {
		case 24 => 17
		case _ => 21
	});
	var v_int_27: int := safe_index_seq(v_seq_7, v_int_26);
	var v_int_28: int := v_int_27;
	var v_seq_8: seq<int> := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_28 := (4 / 12)]) else (v_seq_6));
	var v_int_29: int := v_int_28;
	var v_int_35: int := (if ((|v_seq_8| > 0)) then (v_seq_8[v_int_29]) else (v_int_25));
	var v_seq_9: seq<int> := v_seq_7;
	var v_int_30: int := 4;
	var v_int_31: int := 5;
	var v_int_32: int := 16;
	var v_char_1: char := 'Y';
	var v_real_1: real := m_method_3(v_int_30, v_int_31, v_int_32, v_char_1);
	var v_int_33: int := (v_real_1).Floor;
	var v_int_34: int := safe_index_seq(v_seq_9, v_int_33);
	var v_int_36: int := v_int_34;
	var v_int_37: int := (v_real_1).Floor;
	var v_int_38: int := v_int_28;
	var v_int_39: int, v_int_40: int, v_int_41: int, v_int_42: int := m_method_1(v_int_35, v_int_36, v_int_37, v_int_38);
	v_int_38, v_int_33, v_int_31, v_int_25 := v_int_39, v_int_40, v_int_41, v_int_42;
	var v_seq_10: seq<bool> := ([false, true] + [true]);
	var v_map_7: map<int, int> := map[17 := 8];
	var v_int_43: int := -12;
	var v_int_44: int := (if ((v_int_43 in v_map_7)) then (v_map_7[v_int_43]) else (16));
	var v_seq_19: seq<bool> := v_seq_10;
	var v_int_83: int := v_int_44;
	var v_int_84: int := safe_index_seq(v_seq_19, v_int_83);
	v_int_44 := v_int_84;
	var v_int_45: int := 0;
	var v_int_46: int := 5;
	var v_int_47: int := 13;
	var v_bool_1: bool := m_method_4(v_int_45, v_int_46, v_int_47);
	if ((if ((|v_seq_10| > 0)) then (v_seq_10[v_int_44]) else (v_bool_1)) ==> v_bool_1) {
		var v_int_51: int := v_int_42;
		var v_int_52: int := v_int_33;
		var v_int_53: int := (11 - 15);
		var v_seq_12: seq<int> := [19, 27, 28];
		var v_int_49: int := 7;
		var v_int_50: int := safe_index_seq(v_seq_12, v_int_49);
		var v_int_54: int := v_int_50;
		var v_seq_13: seq<int> := m_method_5(v_int_51, v_int_52, v_int_53, v_int_54);
		var v_seq_14: seq<int> := v_seq_13;
		var v_DT_1_4_1: DT_1<int> := DT_1_4(22, 2);
		var v_DT_1_4_2: DT_1<int> := DT_1_4(20, -15);
		var v_DT_1_4_3: DT_1<int> := DT_1_4(-7, 29);
		var v_DT_1_4_4: DT_1<int> := DT_1_4(5, -16);
		var v_array_1: array<DT_1<int>> := new DT_1<int>[4] [v_DT_1_4_1, v_DT_1_4_2, v_DT_1_4_3, v_DT_1_4_4];
		var v_int_55: int := 16;
		var v_int_56: int := 16;
		var v_int_57: int := safe_division(v_int_55, v_int_56);
		var v_int_58: int := (v_array_1.Length - v_int_57);
		var v_seq_23: seq<int> := v_seq_14;
		var v_int_91: int := v_int_58;
		var v_int_92: int := safe_index_seq(v_seq_23, v_int_91);
		v_int_58 := v_int_92;
		var v_char_3: char := v_char_1;
		var v_array_19: array<int> := m_method_6(v_char_3);
		v_int_26, v_int_46, v_int_35 := (if ((|v_seq_14| > 0)) then (v_seq_14[v_int_58]) else (v_int_57)), v_int_25, v_array_19.Length;
		print "v_DT_1_4_4", " ", v_DT_1_4_4, " ", "v_DT_1_4_3", " ", v_DT_1_4_3, " ", "v_DT_1_4_2", " ", v_DT_1_4_2, " ", "v_DT_1_4_1", " ", v_DT_1_4_1, " ", "v_DT_1_4_4.DT_1_4_1", " ", v_DT_1_4_4.DT_1_4_1, " ", "v_DT_1_4_4.DT_1_4_2", " ", v_DT_1_4_4.DT_1_4_2, " ", "v_DT_1_4_1.DT_1_4_2", " ", v_DT_1_4_1.DT_1_4_2, " ", "v_DT_1_4_1.DT_1_4_1", " ", v_DT_1_4_1.DT_1_4_1, " ", "v_seq_14", " ", v_seq_14, " ", "v_int_46", " ", v_int_46, " ", "v_int_49", " ", v_int_49, " ", "v_seq_12", " ", v_seq_12, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_int_26", " ", v_int_26, " ", "v_seq_13", " ", v_seq_13, " ", "v_array_19", " ", "v_array_1[2]", " ", v_array_1[2], " ", "v_DT_1_4_3.DT_1_4_2", " ", v_DT_1_4_3.DT_1_4_2, " ", "v_array_1[0]", " ", v_array_1[0], " ", "v_DT_1_4_3.DT_1_4_1", " ", v_DT_1_4_3.DT_1_4_1, " ", "v_char_3", " ", (v_char_3 == 'Y'), " ", "v_DT_1_4_2.DT_1_4_2", " ", v_DT_1_4_2.DT_1_4_2, " ", "v_int_57", " ", v_int_57, " ", "v_int_35", " ", v_int_35, " ", "v_DT_1_4_2.DT_1_4_1", " ", v_DT_1_4_2.DT_1_4_1, " ", "v_int_56", " ", v_int_56, " ", "v_int_55", " ", v_int_55, " ", "v_int_54", " ", v_int_54, " ", "v_int_58", " ", v_int_58, " ", "v_array_1[1]", " ", v_array_1[1], " ", "v_int_53", " ", v_int_53, " ", "v_int_52", " ", v_int_52, " ", "v_int_51", " ", v_int_51, " ", "v_array_1[3]", " ", v_array_1[3], " ", "v_int_50", " ", v_int_50, " ", "v_bool_1", " ", v_bool_1, " ", "v_int_46", " ", v_int_46, " ", "v_int_45", " ", v_int_45, " ", "v_int_44", " ", v_int_44, " ", "v_int_43", " ", v_int_43, " ", "v_int_28", " ", v_int_28, " ", "v_seq_10", " ", v_seq_10, " ", "v_int_27", " ", v_int_27, " ", "v_int_26", " ", v_int_26, " ", "v_int_25", " ", v_int_25, " ", "v_int_47", " ", v_int_47, " ", "v_int_42", " ", v_int_42, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, " ", "v_char_1", " ", (v_char_1 == 'Y'), " ", "v_map_7", " ", (v_map_7 == map[17 := 8]), " ", "v_int_29", " ", v_int_29, " ", "v_seq_9", " ", v_seq_9, " ", "v_seq_8", " ", v_seq_8, " ", "v_int_35", " ", v_int_35, " ", "v_seq_7", " ", v_seq_7, " ", "v_int_34", " ", v_int_34, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_33", " ", v_int_33, " ", "v_seq_5", " ", v_seq_5, " ", "v_int_32", " ", v_int_32, " ", "v_int_39", " ", v_int_39, " ", "v_int_38", " ", v_int_38, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_real_1", " ", (v_real_1 == 1.27), " ", "v_int_31", " ", v_int_31, " ", "v_int_30", " ", v_int_30, "\n";
		return ;
	}
	return ;
}

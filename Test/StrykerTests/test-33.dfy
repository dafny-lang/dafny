// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_3 | DT_1_4(DT_1_4_1: T_1, DT_1_4_2: seq<bool>)
datatype DT_2<T_3> = DT_2_1 | DT_2_2(DT_2_2_1: T_3) | DT_2_3(DT_2_3_1: T_3, DT_2_3_2: T_3, DT_2_3_3: T_3) | DT_2_4(DT_2_4_1: T_3, DT_2_4_2: T_3, DT_2_4_3: T_3, DT_2_4_4: T_3)
datatype DT_3 = DT_3_1
datatype DT_4<T_4, T_5> = DT_4_1 | DT_4_2(DT_4_2_1: T_4, DT_4_2_2: T_5, DT_4_2_3: T_5) | DT_4_3(DT_4_3_1: T_4, DT_4_3_2: T_4, DT_4_3_3: T_5)
datatype DT_5<T_6> = DT_5_1 | DT_5_3
datatype DT_6 = DT_6_1 | DT_6_4(DT_6_4_1: bool, DT_6_4_2: real, DT_6_4_3: int)
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

method m_method_6(p_m_method_6_1: (int, real), p_m_method_6_2: (int, real), p_m_method_6_3: bool) returns (ret_1: ((bool, bool, bool), real, int))
{
	var v_bool_bool_bool_1: (bool, bool, bool) := (false, false, false);
	var v_bool_bool_bool_real_int_1: ((bool, bool, bool), real, int) := (v_bool_bool_bool_1, -12.32, 0);
	var v_bool_bool_bool_2: (bool, bool, bool) := (true, false, false);
	var v_bool_bool_bool_real_int_2: ((bool, bool, bool), real, int) := (v_bool_bool_bool_2, 7.46, 14);
	var v_seq_10: seq<((bool, bool, bool), real, int)> := [v_bool_bool_bool_real_int_1, v_bool_bool_bool_real_int_2];
	var v_int_22: int := -6;
	var v_bool_bool_bool_3: (bool, bool, bool) := (false, false, false);
	var v_bool_bool_bool_real_int_3: ((bool, bool, bool), real, int) := (v_bool_bool_bool_3, -11.59, 25);
	return (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_22]) else (v_bool_bool_bool_real_int_3));
}

method m_method_5(p_m_method_5_1: DT_2<bool>) returns (ret_1: real)
{
	return -21.95;
}

method m_method_4(p_m_method_4_1: bool, p_m_method_4_2: bool) returns (ret_1: real)
{
	var v_DT_2_4_1: DT_2<bool> := DT_2_4(true, true, false, false);
	var v_DT_2_4_2: DT_2<bool> := v_DT_2_4_1;
	var v_real_8: real := m_method_5(v_DT_2_4_2);
	return v_real_8;
}

method m_method_3(p_m_method_3_1: bool, p_m_method_3_2: bool, p_m_method_3_3: bool) returns (ret_1: bool)
{
	var v_bool_2: bool, v_bool_3: bool, v_bool_4: bool := false, false, true;
	if false {
		return false;
	}
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

method m_method_2(p_m_method_2_1: bool, p_m_method_2_2: bool, p_m_method_2_3: bool) returns (ret_1: bool)
{
	var v_map_9: map<bool, bool> := map[false := true, true := false];
	var v_bool_1: bool := true;
	return (if ((v_bool_1 in v_map_9)) then (v_map_9[v_bool_1]) else (false));
}

method m_method_1(p_m_method_1_1: real, p_m_method_1_2: real, p_m_method_1_3: int) returns (ret_1: real)
{
	var v_map_7: map<real, set<int>> := map[-15.90 := {15, 3}, -10.70 := {}, -13.03 := {}, -9.12 := {}];
	var v_real_6: real := -12.08;
	var v_map_8: map<real, set<int>> := map[27.05 := {}];
	var v_real_7: real := -4.92;
	if ((if ((v_real_6 in v_map_7)) then (v_map_7[v_real_6]) else ({26, 8})) !! (if ((v_real_7 in v_map_8)) then (v_map_8[v_real_7]) else ({19}))) {
		assert true;
		expect true;
		var v_seq_9: seq<bool> := [true];
		var v_int_18: int := 25;
		var v_bool_9: bool := (if (true) then (true) else (false));
		var v_bool_10: bool := (match false {
			case _ => false
		});
		var v_bool_5: bool := false;
		var v_bool_6: bool := false;
		var v_bool_7: bool := false;
		var v_bool_8: bool := m_method_3(v_bool_5, v_bool_6, v_bool_7);
		var v_bool_11: bool := v_bool_8;
		var v_bool_12: bool := m_method_2(v_bool_9, v_bool_10, v_bool_11);
		v_bool_9, v_bool_12, v_bool_11, v_bool_10 := ((if (false) then (true) else (false)) <==> (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_18]) else (true))), v_bool_12, v_bool_12, v_bool_12;
		var v_int_19: int := -26;
		var v_int_20: int := 19;
		var v_int_21: int := safe_division(v_int_19, v_int_20);
		match (p_m_method_1_3 - v_int_21) {
			case _ => {
				var v_seq_16: seq<bool> := [false, true];
				var v_seq_17: seq<bool> := (if ((|v_seq_16| > 0)) then (v_seq_16[9..9]) else (v_seq_16));
				var v_int_35: int := (26 + 14);
				if (if ((|v_seq_17| > 0)) then (v_seq_17[v_int_35]) else (v_bool_8)) {
					
				}
				return v_real_6;
			}
			
		}
		
	}
	return (if ((7 != -22)) then (p_m_method_1_2) else ((if (true) then (-25.69) else (14.69))));
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_map_1: map<multiset<real>, int> := map[multiset{-19.50} := 21, multiset({27.32, -19.67, -7.21, -28.45}) := 21];
	var v_multiset_1: multiset<real> := multiset{5.90, 2.87, -6.14};
	var v_int_7: int := (1 / ((if ((v_multiset_1 in v_map_1)) then (v_map_1[v_multiset_1]) else (10)) - (if (false) then (0) else (8))));
	var v_map_2: map<real, char> := map[28.70 := 'h'];
	var v_real_1: real := 12.62;
	var v_map_3: map<real, seq<int>> := map[15.64 := [8], 16.83 := [], -12.14 := [20]];
	var v_real_2: real := -6.84;
	var v_seq_3: seq<int> := (if ((v_real_2 in v_map_3)) then (v_map_3[v_real_2]) else ([16, 14, -22]));
	var v_int_9: int := (match -11.79 {
		case -3.35 => 27
		case _ => 10
	});
	var v_seq_48: seq<int> := v_seq_3;
	var v_int_81: int := v_int_9;
	var v_int_82: int := safe_index_seq(v_seq_48, v_int_81);
	v_int_9 := v_int_82;
	var v_int_8: int := (if (((if ((v_real_1 in v_map_2)) then (v_map_2[v_real_1]) else ('n')) <= 'Q')) then (v_int_7) else ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_9]) else (v_int_9))));
	while (v_int_7 < v_int_8) 
		decreases v_int_8 - v_int_7;
		invariant (v_int_7 <= v_int_8);
	{
		v_int_7 := (v_int_7 + 1);
		assert ((v_real_2 == -6.84));
		expect ((v_real_2 == -6.84));
		var v_map_4: map<real, set<real>> := map[12.71 := {-14.91, -5.45, -12.91, 12.14}, -12.77 := {17.35, 8.70}, 29.13 := {}];
		var v_real_3: real := -28.23;
		var v_map_5: map<real, int> := ((map[15.02 := 27, -1.63 := 0, 8.22 := 9, 13.22 := 25, -25.93 := -4] - {}) - (if ((v_real_3 in v_map_4)) then (v_map_4[v_real_3]) else ({})));
		var v_real_4: real := v_real_1;
		var v_int_10: int := (if ((v_real_4 in v_map_5)) then (v_map_5[v_real_4]) else ((match -24.46 {
			case -12.22 => 6
			case 4.57 => |multiset{24.86}|
			case _ => 26
		})));
		var v_seq_4: seq<bool> := (match 5.67 {
			case 11.07 => [false]
			case 5.34 => [true, true]
			case _ => [false, true, true]
		});
		var v_int_12: int := v_int_7;
		var v_seq_5: seq<int> := [];
		var v_seq_6: seq<int> := v_seq_5;
		var v_int_13: int := 23;
		var v_int_14: int := safe_index_seq(v_seq_6, v_int_13);
		var v_int_15: int := v_int_14;
		var v_seq_8: seq<int> := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_15 := 20]) else (v_seq_5));
		var v_seq_7: seq<int> := [8, 26, 11, 7];
		var v_int_16: int := 6;
		var v_seq_49: seq<int> := v_seq_7;
		var v_int_83: int := v_int_16;
		var v_int_84: int := safe_index_seq(v_seq_49, v_int_83);
		v_int_16 := v_int_84;
		var v_int_17: int := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_16]) else (15));
		var v_map_6: map<real, int> := map[0.03 := 16, -16.05 := 26, 25.88 := 24];
		var v_real_5: real := 3.58;
		var v_int_11: int := (if ((if ((|v_seq_4| > 0)) then (v_seq_4[v_int_12]) else ((if (true) then (true) else (false))))) then ((v_int_9 / (-9.71).Floor)) else ((if ((|v_seq_8| > 0)) then (v_seq_8[v_int_17]) else ((if ((v_real_5 in v_map_6)) then (v_map_6[v_real_5]) else (8))))));
		while (v_int_10 < v_int_11) 
			decreases v_int_11 - v_int_10;
			invariant (v_int_10 <= v_int_11);
		{
			v_int_10 := (v_int_10 + 1);
			return ;
		}
		print "v_map_5", " ", (v_map_5 == map[-1.63 := 0, 13.22 := 25, 15.02 := 27, -25.93 := -4, 8.22 := 9]), " ", "v_map_4", " ", (v_map_4 == map[29.13 := {}, -12.77 := {8.70, 17.35}, 12.71 := {-14.91, -5.45, 12.14, -12.91}]), " ", "v_map_6", " ", (v_map_6 == map[25.88 := 24, -16.05 := 26, 0.03 := 16]), " ", "v_int_13", " ", v_int_13, " ", "v_seq_8", " ", v_seq_8, " ", "v_int_12", " ", v_int_12, " ", "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_11", " ", v_int_11, " ", "v_int_10", " ", v_int_10, " ", "v_seq_5", " ", v_seq_5, " ", "v_seq_4", " ", v_seq_4, " ", "v_int_17", " ", v_int_17, " ", "v_int_16", " ", v_int_16, " ", "v_int_15", " ", v_int_15, " ", "v_int_14", " ", v_int_14, " ", "v_real_3", " ", (v_real_3 == -28.23), " ", "v_real_4", " ", (v_real_4 == 12.62), " ", "v_real_5", " ", (v_real_5 == 3.58), " ", "v_seq_3", " ", v_seq_3, " ", "v_int_9", " ", v_int_9, " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_real_1", " ", (v_real_1 == 12.62), " ", "v_real_2", " ", (v_real_2 == -6.84), " ", "v_multiset_1", " ", (v_multiset_1 == multiset{5.90, -6.14, 2.87}), " ", "v_map_1", " ", (v_map_1 == map[multiset{-19.50} := 21, multiset{-7.21, 27.32, -28.45, -19.67} := 21]), " ", "v_map_3", " ", (v_map_3 == map[15.64 := [8], -12.14 := [20], 16.83 := []]), " ", "v_map_2", " ", (v_map_2 == map[28.70 := 'h']), "\n";
		return ;
	}
	var v_real_11: real := v_real_2;
	var v_DT_2_2_1: DT_2<real> := DT_2_2(26.10);
	var v_DT_2_2_2: DT_2<real> := DT_2_2(2.65);
	var v_DT_2_2_3: DT_2<real> := DT_2_2(-25.30);
	var v_map_11: map<DT_2<real>, real> := (if (true) then (map[v_DT_2_2_1 := -22.13]) else (map[v_DT_2_2_2 := -20.53, v_DT_2_2_3 := 12.88]));
	var v_DT_2_2_4: DT_2<real> := DT_2_2(-23.07);
	var v_DT_2_2_5: DT_2<real> := DT_2_2(-20.24);
	var v_seq_18: seq<DT_2<real>> := [v_DT_2_2_4, v_DT_2_2_5];
	var v_int_36: int := 12;
	var v_DT_2_2_6: DT_2<real> := DT_2_2(6.13);
	var v_DT_2_2_7: DT_2<real> := (if ((|v_seq_18| > 0)) then (v_seq_18[v_int_36]) else (v_DT_2_2_6));
	var v_bool_20: bool := true;
	var v_bool_21: bool := true;
	var v_real_10: real := m_method_4(v_bool_20, v_bool_21);
	var v_real_12: real := (if ((v_DT_2_2_7 in v_map_11)) then (v_map_11[v_DT_2_2_7]) else (v_real_10));
	var v_seq_19: seq<set<real>> := [{12.01, -23.97, -20.93, -18.80}, {24.19}, {-6.54, -12.54}, {-17.16}];
	var v_int_37: int := 21;
	var v_int_38: int := |(if ((|v_seq_19| > 0)) then (v_seq_19[v_int_37]) else ({27.51, -2.28}))|;
	var v_real_13: real := m_method_1(v_real_11, v_real_12, v_int_38);
	v_real_1, v_real_11, v_real_10 := v_real_2, v_real_1, v_real_13;
	var v_seq_20: seq<char> := ['c'];
	var v_int_39: int := 4;
	var v_DT_2_3_1: DT_2<real> := DT_2_3(-18.34, -18.59, 3.64);
	var v_DT_2_3_bool_map_1: (DT_2<real>, bool, map<bool, bool>) := (v_DT_2_3_1, true, map[true := true, true := false, false := true, false := false]);
	var v_map_12: map<(DT_2<real>, bool, map<bool, bool>), char> := map[v_DT_2_3_bool_map_1 := 'L'];
	var v_DT_2_3_2: DT_2<real> := DT_2_3(19.18, 13.66, -5.78);
	var v_DT_2_3_bool_map_2: (DT_2<real>, bool, map<bool, bool>) := (v_DT_2_3_2, true, map[false := true, true := false]);
	var v_DT_2_3_bool_map_3: (DT_2<real>, bool, map<bool, bool>) := v_DT_2_3_bool_map_2;
	var v_seq_21: seq<char> := [];
	var v_seq_23: seq<char> := (if ((|v_seq_21| > 0)) then (v_seq_21[1..2]) else (v_seq_21));
	var v_seq_22: seq<int> := [18, 21, 28];
	var v_int_40: int := -18;
	var v_int_41: int := (if ((|v_seq_22| > 0)) then (v_seq_22[v_int_40]) else (-13));
	var v_map_13: map<char, bool> := map['G' := true, 'F' := true, 'W' := false, 'k' := true];
	var v_char_1: char := 'M';
	var v_seq_map_1: (seq<bool>, map<real, bool>) := ([false, false, false], map[-0.17 := false, -0.72 := false, -2.90 := false, 16.52 := false]);
	var v_seq_map_2: (seq<bool>, map<real, bool>) := ([true, true, false, true], map[3.04 := true, 21.75 := true, -20.73 := false, 20.28 := false]);
	var v_seq_map_3: (seq<bool>, map<real, bool>) := ([false, true, false, false], map[12.26 := false, 1.41 := true]);
	var v_seq_map_4: (seq<bool>, map<real, bool>) := ([true, false], map[11.52 := true, -26.61 := false]);
	var v_seq_map_5: (seq<bool>, map<real, bool>) := ([], map[8.66 := false, 17.60 := true, -26.67 := false, 11.44 := true, 21.71 := true]);
	var v_seq_map_6: (seq<bool>, map<real, bool>) := ([false, false, true], map[-12.78 := false, -25.92 := true, -24.50 := true]);
	var v_seq_map_7: (seq<bool>, map<real, bool>) := ([true, true], map[-19.57 := true]);
	var v_seq_map_8: (seq<bool>, map<real, bool>) := ([], map[-6.43 := false]);
	var v_seq_map_9: (seq<bool>, map<real, bool>) := ([false], map[6.05 := true, 26.79 := true]);
	var v_map_14: map<(seq<bool>, map<real, bool>), char> := (map[v_seq_map_1 := 'T', v_seq_map_2 := 'W', v_seq_map_3 := 'D', v_seq_map_4 := 'P', v_seq_map_5 := 'Z'] + map[v_seq_map_6 := 'k', v_seq_map_7 := 'l', v_seq_map_8 := 'm', v_seq_map_9 := 'e']);
	var v_seq_map_10: (seq<bool>, map<real, bool>) := ([], map[23.01 := false, 22.00 := true, -29.47 := false]);
	var v_seq_map_11: (seq<bool>, map<real, bool>) := ([false, true, false], map[-22.03 := true, 16.33 := false, 18.71 := false]);
	var v_seq_map_12: (seq<bool>, map<real, bool>) := (if (false) then (v_seq_map_10) else (v_seq_map_11));
	var v_map_16: map<int, char> := (if (false) then (map[29 := 'f', 18 := 'L', -15 := 'R', 1 := 'A']) else (map[17 := 'H', 6 := 'Y']));
	var v_int_42: int := v_int_8;
	var v_map_15: map<multiset<map<bool, real>>, char> := map[multiset{map[true := 29.78], map[true := 14.80, false := 22.08, false := 15.64, true := 21.41]} := 'K', multiset{} := 'v', multiset{map[false := 29.03, false := -22.13, false := 8.12], map[false := -8.06, true := 7.26, true := -11.13, false := -29.35], map[false := -11.06, false := 11.37]} := 'S', multiset{} := 'H'];
	var v_multiset_2: multiset<map<bool, real>> := multiset({});
	var v_DT_3_1_1: DT_3 := DT_3_1;
	var v_DT_3_1_2: DT_3 := DT_3_1;
	var v_DT_3_1_3: DT_3 := DT_3_1;
	var v_DT_4_1_1: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_4: DT_3 := DT_3_1;
	var v_DT_3_1_5: DT_3 := DT_3_1;
	var v_DT_3_1_6: DT_3 := DT_3_1;
	var v_DT_3_1_7: DT_3 := DT_3_1;
	var v_DT_4_1_2: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_8: DT_3 := DT_3_1;
	var v_DT_3_1_9: DT_3 := DT_3_1;
	var v_DT_4_1_3: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_10: DT_3 := DT_3_1;
	var v_DT_3_1_11: DT_3 := DT_3_1;
	var v_DT_3_1_12: DT_3 := DT_3_1;
	var v_DT_3_1_13: DT_3 := DT_3_1;
	var v_DT_4_1_4: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_5: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_6: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_14: DT_3 := DT_3_1;
	var v_DT_4_1_7: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_15: DT_3 := DT_3_1;
	var v_DT_3_1_16: DT_3 := DT_3_1;
	var v_DT_3_1_17: DT_3 := DT_3_1;
	var v_DT_3_1_18: DT_3 := DT_3_1;
	var v_DT_4_1_8: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_19: DT_3 := DT_3_1;
	var v_DT_3_1_20: DT_3 := DT_3_1;
	var v_DT_4_1_9: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_21: DT_3 := DT_3_1;
	var v_DT_3_1_22: DT_3 := DT_3_1;
	var v_DT_4_1_10: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_23: DT_3 := DT_3_1;
	var v_DT_3_1_24: DT_3 := DT_3_1;
	var v_DT_4_1_11: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_25: DT_3 := DT_3_1;
	var v_DT_3_1_26: DT_3 := DT_3_1;
	var v_DT_4_1_12: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_13: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_27: DT_3 := DT_3_1;
	var v_DT_4_1_14: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_28: DT_3 := DT_3_1;
	var v_DT_3_1_29: DT_3 := DT_3_1;
	var v_DT_3_1_30: DT_3 := DT_3_1;
	var v_DT_4_1_15: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_31: DT_3 := DT_3_1;
	var v_DT_4_1_16: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_map_18: map<char, map<multiset<DT_3>, DT_4<set<bool>, set<real>>>> := map['h' := map[multiset{v_DT_3_1_1, v_DT_3_1_2, v_DT_3_1_3} := v_DT_4_1_1, multiset{v_DT_3_1_4, v_DT_3_1_5, v_DT_3_1_6, v_DT_3_1_7} := v_DT_4_1_2, multiset{v_DT_3_1_8, v_DT_3_1_9} := v_DT_4_1_3, multiset({v_DT_3_1_10, v_DT_3_1_11, v_DT_3_1_12, v_DT_3_1_13}) := v_DT_4_1_4, multiset{} := v_DT_4_1_5], 'Y' := map[multiset{} := v_DT_4_1_6, multiset{v_DT_3_1_14} := v_DT_4_1_7], 'V' := map[multiset({v_DT_3_1_15, v_DT_3_1_16, v_DT_3_1_17, v_DT_3_1_18}) := v_DT_4_1_8, multiset{v_DT_3_1_19, v_DT_3_1_20} := v_DT_4_1_9, multiset({v_DT_3_1_21, v_DT_3_1_22}) := v_DT_4_1_10], 'S' := map[multiset{v_DT_3_1_23, v_DT_3_1_24} := v_DT_4_1_11, multiset({v_DT_3_1_25, v_DT_3_1_26}) := v_DT_4_1_12, multiset({}) := v_DT_4_1_13]]['K' := map[multiset{v_DT_3_1_27} := v_DT_4_1_14, multiset({v_DT_3_1_28, v_DT_3_1_29, v_DT_3_1_30}) := v_DT_4_1_15, multiset{v_DT_3_1_31} := v_DT_4_1_16]];
	var v_map_17: map<seq<seq<int>>, char> := map[[[], [7, 7]] := 'f', [[28, 12, 4, 21]] := 's', [[], [24, 8, -22], [25]] := 'h'];
	var v_seq_24: seq<seq<int>> := [];
	var v_char_2: char := (if ((v_seq_24 in v_map_17)) then (v_map_17[v_seq_24]) else ('S'));
	var v_DT_3_1_32: DT_3 := DT_3_1;
	var v_DT_3_1_33: DT_3 := DT_3_1;
	var v_DT_3_1_34: DT_3 := DT_3_1;
	var v_DT_4_1_17: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_35: DT_3 := DT_3_1;
	var v_DT_3_1_36: DT_3 := DT_3_1;
	var v_DT_4_1_18: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_37: DT_3 := DT_3_1;
	var v_DT_3_1_38: DT_3 := DT_3_1;
	var v_DT_4_1_19: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_39: DT_3 := DT_3_1;
	var v_DT_3_1_40: DT_3 := DT_3_1;
	var v_DT_3_1_41: DT_3 := DT_3_1;
	var v_DT_4_1_20: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_3_1_42: DT_3 := DT_3_1;
	var v_DT_3_1_43: DT_3 := DT_3_1;
	var v_DT_3_1_44: DT_3 := DT_3_1;
	var v_DT_4_1_21: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_map_20: map<multiset<DT_3>, DT_4<set<bool>, set<real>>> := (if ((v_char_2 in v_map_18)) then (v_map_18[v_char_2]) else ((map[multiset{v_DT_3_1_32, v_DT_3_1_33, v_DT_3_1_34} := v_DT_4_1_17, multiset({v_DT_3_1_35, v_DT_3_1_36}) := v_DT_4_1_18, multiset{v_DT_3_1_37, v_DT_3_1_38} := v_DT_4_1_19, multiset{v_DT_3_1_39, v_DT_3_1_40, v_DT_3_1_41} := v_DT_4_1_20, multiset{v_DT_3_1_42, v_DT_3_1_43, v_DT_3_1_44} := v_DT_4_1_21] - {multiset{}})));
	var v_DT_3_1_45: DT_3 := DT_3_1;
	var v_DT_3_1_46: DT_3 := DT_3_1;
	var v_DT_3_1_47: DT_3 := DT_3_1;
	var v_DT_3_1_48: DT_3 := DT_3_1;
	var v_DT_3_1_49: DT_3 := DT_3_1;
	var v_DT_3_1_50: DT_3 := DT_3_1;
	var v_DT_3_1_51: DT_3 := DT_3_1;
	var v_DT_3_1_52: DT_3 := DT_3_1;
	var v_DT_3_1_53: DT_3 := DT_3_1;
	var v_seq_25: seq<multiset<DT_3>> := [];
	var v_int_43: int := 13;
	var v_DT_3_1_54: DT_3 := DT_3_1;
	var v_DT_3_1_55: DT_3 := DT_3_1;
	var v_multiset_3: multiset<DT_3> := (match false {
		case _ => (if ((|v_seq_25| > 0)) then (v_seq_25[v_int_43]) else (multiset{v_DT_3_1_54, v_DT_3_1_55}))
	});
	var v_DT_4_1_22: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_23: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_24: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_25: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_26: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_27: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_28: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_DT_4_1_29: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_seq_26: seq<DT_4<set<bool>, set<real>>> := (match 16 {
		case _ => [v_DT_4_1_27, v_DT_4_1_28, v_DT_4_1_29]
	});
	var v_int_44: int := (match 28 {
		case _ => 4
	});
	var v_DT_4_1_30: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_map_19: map<int, DT_4<set<bool>, set<real>>> := map[16 := v_DT_4_1_30];
	var v_int_45: int := 14;
	var v_DT_4_1_31: DT_4<set<bool>, set<real>> := DT_4_1;
	var v_char_3: char, v_char_4: char, v_DT_4_1_32: DT_4<set<bool>, set<real>> := (match true {
		case _ => (if ((if ((v_char_1 in v_map_13)) then (v_map_13[v_char_1]) else (true))) then (v_char_1) else ((if (true) then ('Y') else ('r'))))
	}), (if (!(v_bool_20)) then ((if ((v_seq_map_12 in v_map_14)) then (v_map_14[v_seq_map_12]) else ((if (true) then ('q') else ('W'))))) else ((if ((v_int_42 in v_map_16)) then (v_map_16[v_int_42]) else ((if ((v_multiset_2 in v_map_15)) then (v_map_15[v_multiset_2]) else ('h')))))), (if ((v_multiset_3 in v_map_20)) then (v_map_20[v_multiset_3]) else ((if ((|v_seq_26| > 0)) then (v_seq_26[v_int_44]) else ((if ((v_int_45 in v_map_19)) then (v_map_19[v_int_45]) else (v_DT_4_1_31))))));
	var v_seq_27: seq<int> := [];
	var v_seq_28: seq<int> := v_seq_27;
	var v_int_47: int := 24;
	var v_int_48: int := safe_index_seq(v_seq_28, v_int_47);
	var v_int_49: int := v_int_48;
	var v_seq_29: seq<int> := (if ((|v_seq_27| > 0)) then (v_seq_27[v_int_49 := 6]) else (v_seq_27));
	var v_map_21: map<int, int> := map[18 := 16, 15 := 2];
	var v_int_50: int := 24;
	var v_seq_31: seq<int> := (if ((|v_seq_29| > 0)) then (v_seq_29[(if ((v_int_50 in v_map_21)) then (v_map_21[v_int_50]) else (17))..0]) else (v_seq_29));
	var v_seq_30: seq<int> := v_seq_3;
	var v_map_22: map<int, int> := map[4 := 17, 3 := 21, 11 := 17, -3 := 18, -14 := 18];
	var v_int_51: int := 27;
	var v_int_52: int := (if ((v_int_51 in v_map_22)) then (v_map_22[v_int_51]) else (13));
	var v_int_53: int := (if ((|v_seq_30| > 0)) then (v_seq_30[v_int_52]) else ((match -28 {
		case _ => 16
	})));
	var v_map_23: map<int, int> := map[6 := 18, 26 := 25, 27 := 27, 20 := 5, -26 := 21];
	var v_int_54: int := 3;
	var v_int_79: int, v_int_80: int := (v_int_42 % |(match 10 {
		case _ => map[7 := 11, 26 := -5]
	})|), (if ((|v_seq_31| > 0)) then (v_seq_31[v_int_53]) else ((match 4 {
		case _ => (if ((v_int_54 in v_map_23)) then (v_map_23[v_int_54]) else (-14))
	})));
	for v_int_46 := v_int_79 to v_int_80 
		invariant (v_int_80 - v_int_46 >= 0)
	{
		var v_map_24: map<seq<set<int>>, seq<int>> := map[[{27, 14, 23, 2}, {15, -14, 10, -10}, {4, 5, 14, 12}, {14, 27}] := [15], [{23, 9, 0, 20}, {4, 19, 3}] := [-4, 8]];
		var v_seq_32: seq<set<int>> := [{25, 4}, {13, 22}, {3}, {23, -17}];
		var v_seq_33: seq<int> := (if ((v_seq_32 in v_map_24)) then (v_map_24[v_seq_32]) else ([3]));
		var v_map_25: map<char, int> := map['G' := 21];
		var v_char_5: char := 'p';
		var v_int_55: int := (if ((v_char_5 in v_map_25)) then (v_map_25[v_char_5]) else (11));
		var v_map_26: map<seq<map<int, bool>>, int> := (map[[map[1 := false, 14 := false, 10 := true], map[17 := true, 19 := true, 6 := false, -29 := true]] := 7, [map[27 := true, 5 := false, 27 := false, 19 := false], map[21 := true, 10 := false, 24 := false, 12 := false, 21 := false], map[3 := true, 9 := true, 22 := false]] := 21, [map[7 := false, 28 := true], map[17 := true, 2 := true, 8 := true, 6 := true, 1 := false], map[18 := false, 21 := true, -24 := true, 11 := false, 24 := false], map[23 := false, -2 := true, 7 := true, 10 := true]] := 1] - {});
		var v_seq_34: seq<map<int, bool>> := [map[0 := true, 17 := false, 16 := false, 29 := true, 22 := true], map[-19 := false], map[29 := false, 14 := true, 15 := true, 27 := false], map[27 := true, 28 := true, 28 := true, 25 := true]];
		var v_seq_35: seq<map<int, bool>> := v_seq_34;
		var v_int_56: int := 0;
		var v_int_57: int := safe_index_seq(v_seq_35, v_int_56);
		var v_int_58: int := v_int_57;
		var v_seq_36: seq<map<int, bool>> := (if ((|v_seq_34| > 0)) then (v_seq_34[v_int_58 := map[0 := false, 19 := true, 29 := false, 24 := true]]) else (v_seq_34));
		var v_seq_37: seq<int> := [];
		var v_seq_38: seq<int> := v_seq_37;
		var v_int_59: int := 20;
		var v_int_60: int := safe_index_seq(v_seq_38, v_int_59);
		var v_int_61: int := v_int_60;
		var v_seq_40: seq<int> := (if ((match 7 {
			case _ => false
		})) then ((if ((|v_seq_37| > 0)) then (v_seq_37[v_int_61 := 17]) else (v_seq_37))) else ((if (true) then ([16, 5, 3, 17]) else ([26, 25]))));
		var v_map_27: map<bool, int> := map[true := 1, true := 7, true := 13, false := 18];
		var v_bool_22: bool := true;
		var v_seq_39: seq<int> := [9, -18, 14];
		var v_int_62: int := 27;
		var v_int_63: int := ((if ((v_bool_22 in v_map_27)) then (v_map_27[v_bool_22]) else (24)) + (if ((|v_seq_39| > 0)) then (v_seq_39[v_int_62]) else (12)));
		var v_DT_2_2_8: DT_2<real> := DT_2_2(-18.18);
		var v_DT_2_2_9: DT_2<real> := DT_2_2(-28.73);
		var v_DT_2_2_10: DT_2<real> := DT_2_2(-11.42);
		var v_DT_2_2_11: DT_2<real> := DT_2_2(-9.73);
		var v_DT_2_2_12: DT_2<real> := DT_2_2(9.62);
		var v_DT_2_2_13: DT_2<real> := DT_2_2(-14.39);
		var v_DT_2_2_14: DT_2<real> := DT_2_2(-25.89);
		var v_DT_2_2_15: DT_2<real> := DT_2_2(25.48);
		var v_DT_2_2_16: DT_2<real> := DT_2_2(-25.47);
		var v_DT_2_2_17: DT_2<real> := DT_2_2(-6.97);
		var v_DT_2_2_18: DT_2<real> := DT_2_2(-2.56);
		var v_DT_2_2_19: DT_2<real> := DT_2_2(-9.29);
		var v_DT_2_2_20: DT_2<real> := DT_2_2(-10.63);
		var v_DT_2_2_21: DT_2<real> := DT_2_2(29.95);
		var v_seq_41: seq<map<DT_2<real>, char>> := [map[v_DT_2_2_8 := 'v', v_DT_2_2_9 := 'Z', v_DT_2_2_10 := 'I', v_DT_2_2_11 := 'F', v_DT_2_2_12 := 'q'], map[v_DT_2_2_13 := 'Q', v_DT_2_2_14 := 'C', v_DT_2_2_15 := 'R', v_DT_2_2_16 := 'S'], map[v_DT_2_2_17 := 't', v_DT_2_2_18 := 'h', v_DT_2_2_19 := 'E', v_DT_2_2_20 := 'N', v_DT_2_2_21 := 'U']];
		var v_seq_42: seq<map<DT_2<real>, char>> := v_seq_41;
		var v_int_64: int := 3;
		var v_int_65: int := safe_index_seq(v_seq_42, v_int_64);
		var v_int_66: int := v_int_65;
		var v_DT_2_2_22: DT_2<real> := DT_2_2(14.53);
		var v_DT_2_2_23: DT_2<real> := DT_2_2(12.25);
		var v_DT_2_2_24: DT_2<real> := DT_2_2(22.15);
		var v_DT_2_2_25: DT_2<real> := DT_2_2(13.08);
		var v_DT_2_2_26: DT_2<real> := DT_2_2(-24.04);
		var v_seq_44: seq<map<DT_2<real>, char>> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_66 := map[v_DT_2_2_22 := 'y', v_DT_2_2_23 := 'E', v_DT_2_2_24 := 'i', v_DT_2_2_25 := 'Y', v_DT_2_2_26 := 'D']]) else (v_seq_41));
		var v_seq_45: seq<map<DT_2<real>, char>> := v_seq_44;
		var v_int_68: int := (match false {
			case _ => 19
		});
		var v_int_69: int := safe_index_seq(v_seq_45, v_int_68);
		var v_int_70: int := v_int_69;
		var v_DT_2_2_27: DT_2<real> := DT_2_2(-27.29);
		var v_DT_2_2_28: DT_2<real> := DT_2_2(1.46);
		var v_DT_2_2_29: DT_2<real> := DT_2_2(0.66);
		var v_DT_2_2_30: DT_2<real> := DT_2_2(-19.57);
		var v_DT_2_2_31: DT_2<real> := DT_2_2(26.96);
		var v_DT_2_2_32: DT_2<real> := DT_2_2(28.40);
		var v_seq_43: seq<map<DT_2<real>, char>> := [map[v_DT_2_2_27 := 'B', v_DT_2_2_28 := 'R', v_DT_2_2_29 := 'L', v_DT_2_2_30 := 'v', v_DT_2_2_31 := 'g'], map[v_DT_2_2_32 := 'T']];
		var v_int_67: int := 26;
		var v_DT_2_2_33: DT_2<real> := DT_2_2(-22.60);
		var v_DT_2_2_34: DT_2<real> := DT_2_2(9.12);
		var v_DT_2_2_35: DT_2<real> := DT_2_2(29.07);
		var v_seq_46: seq<map<DT_2<real>, char>> := (if ((|v_seq_44| > 0)) then (v_seq_44[v_int_70 := (if ((|v_seq_43| > 0)) then (v_seq_43[v_int_67]) else (map[v_DT_2_2_33 := 'F', v_DT_2_2_34 := 'h', v_DT_2_2_35 := 'a']))]) else (v_seq_44));
		var v_char_set_map_1: (char, set<real>, map<real, bool>) := ('r', {13.59}, map[3.91 := false, 19.83 := false, 11.21 := true, -26.71 := true]);
		var v_char_set_map_2: (char, set<real>, map<real, bool>) := ('o', {23.50}, map[6.50 := true, -6.44 := true, -24.71 := false, -19.91 := true]);
		var v_map_28: map<(char, set<real>, map<real, bool>), int> := map[v_char_set_map_1 := 22, v_char_set_map_2 := 11];
		var v_char_set_map_3: (char, set<real>, map<real, bool>) := ('K', {-7.35}, map[-6.27 := false]);
		var v_char_set_map_4: (char, set<real>, map<real, bool>) := v_char_set_map_3;
		var v_int_71: int := ((if (false) then (24) else (26)) / (if ((v_char_set_map_4 in v_map_28)) then (v_map_28[v_char_set_map_4]) else (21)));
		var v_DT_2_2_36: DT_2<real> := DT_2_2(-8.01);
		var v_DT_2_2_37: DT_2<real> := DT_2_2(21.05);
		var v_DT_2_2_38: DT_2<real> := DT_2_2(4.20);
		var v_DT_2_2_39: DT_2<real> := DT_2_2(-29.41);
		var v_DT_2_2_40: DT_2<real> := DT_2_2(19.14);
		var v_DT_2_2_41: DT_2<real> := DT_2_2(22.26);
		var v_DT_2_2_42: DT_2<real> := DT_2_2(0.76);
		var v_DT_2_2_43: DT_2<real> := DT_2_2(-28.24);
		var v_DT_2_2_44: DT_2<real> := DT_2_2(6.92);
		var v_seq_47: seq<char> := ['q', 'c', 'z', 'W'];
		var v_int_72: int := 4;
		var v_DT_6_1_1: DT_6 := DT_6_1;
		var v_DT_6_1_2: DT_6 := DT_6_1;
		var v_DT_6_1_3: DT_6 := DT_6_1;
		var v_DT_6_1_4: DT_6 := DT_6_1;
		var v_DT_6_1_5: DT_6 := DT_6_1;
		var v_DT_6_1_6: DT_6 := DT_6_1;
		var v_DT_6_1_7: DT_6 := DT_6_1;
		var v_DT_6_1_8: DT_6 := DT_6_1;
		var v_DT_6_1_9: DT_6 := DT_6_1;
		var v_DT_6_1_10: DT_6 := DT_6_1;
		var v_DT_6_1_11: DT_6 := DT_6_1;
		var v_DT_6_1_12: DT_6 := DT_6_1;
		var v_DT_6_1_13: DT_6 := DT_6_1;
		var v_DT_6_1_14: DT_6 := DT_6_1;
		var v_DT_6_1_15: DT_6 := DT_6_1;
		var v_map_29: map<char, DT_6> := map['g' := v_DT_6_1_13, 'W' := v_DT_6_1_14, 'B' := v_DT_6_1_15];
		var v_char_6: char := 'b';
		var v_DT_6_1_16: DT_6 := DT_6_1;
		var v_int_73: int, v_int_74: int, v_int_75: int, v_map_30: map<DT_2<real>, char>, v_map_31: map<DT_6, seq<int>> := (if (v_bool_21) then ((if ((|v_seq_33| > 0)) then (v_seq_33[v_int_55]) else ((if (true) then (7) else (11))))) else ((if ((v_seq_36 in v_map_26)) then (v_map_26[v_seq_36]) else ((13 * 17))))), (if ((|v_seq_40| > 0)) then (v_seq_40[v_int_63]) else (v_int_60)), (v_int_58 % (v_int_7 / (if (false) then (-19) else (7)))), (if ((|v_seq_46| > 0)) then (v_seq_46[v_int_71]) else ((map[v_DT_2_2_36 := 'B', v_DT_2_2_37 := 'P'] + map[v_DT_2_2_38 := 'B', v_DT_2_2_39 := 'C', v_DT_2_2_40 := 'J', v_DT_2_2_41 := 'w', v_DT_2_2_42 := 'w'])[(match 'G' {
			case _ => v_DT_2_2_44
		}) := (if ((|v_seq_47| > 0)) then (v_seq_47[v_int_72]) else ('t'))])), (match 'S' {
			case _ => (map[v_DT_6_1_6 := [19, 11, 18], v_DT_6_1_7 := [], v_DT_6_1_8 := [21, 16], v_DT_6_1_9 := [8, -3, 15], v_DT_6_1_10 := [-10, 0, 18, -17]] + map[v_DT_6_1_11 := [8], v_DT_6_1_12 := []])[(if ((v_char_6 in v_map_29)) then (v_map_29[v_char_6]) else (v_DT_6_1_16)) := (if (true) then ([22, 20, 1, 11]) else ([]))]
		});
		var v_map_32: map<char, bool> := map['o' := false];
		var v_char_7: char := 'F';
		var v_map_33: map<char, bool> := map['y' := true];
		var v_char_8: char := 'b';
		var v_int_77: int, v_int_78: int := (v_real_10).Floor, (if (((if ((v_char_7 in v_map_32)) then (v_map_32[v_char_7]) else (true)) != (if (true) then (true) else (false)))) then ((if ((if ((v_char_8 in v_map_33)) then (v_map_33[v_char_8]) else (true))) then ((if (false) then (13) else (17))) else (v_int_58))) else (v_int_58));
		for v_int_76 := v_int_77 to v_int_78 
			invariant (v_int_78 - v_int_76 >= 0)
		{
			return ;
		}
	}
	assert true;
	expect true;
	assert true;
	expect true;
	return ;
}

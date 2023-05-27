// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
datatype DT_1<T_1, T_2> = DT_1_1 | DT_1_3(DT_1_3_1: T_2, DT_1_3_2: T_2, DT_1_3_3: T_2, DT_1_3_4: T_1)
datatype DT_2<T_3> = DT_2_1 | DT_2_3(DT_2_3_1: T_3, DT_2_3_2: T_3, DT_2_3_3: T_3, DT_2_3_4: T_3) | DT_2_4(DT_2_4_1: T_3, DT_2_4_2: T_3, DT_2_4_3: T_3, DT_2_4_4: T_3)
datatype DT_3 = DT_3_1
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_7(p_m_method_7_1: bool) returns (ret_1: map<int, bool>)
{
	if true {
		return map[-13 := false, 22 := false, 17 := true, 11 := false, 1 := true];
	} else {
		return map[17 := true, 5 := false, 7 := false, 9 := false, 1 := true];
	}
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: int, p_m_method_6_2: int, p_m_method_6_3: int, p_m_method_6_4: int) returns (ret_1: map<int, bool>)
{
	var v_bool_5: bool := false;
	var v_map_9: map<int, bool> := m_method_7(v_bool_5);
	return v_map_9;
}

method m_method_5(p_m_method_5_1: int, p_m_method_5_2: int, p_m_method_5_3: int) returns (ret_1: seq<int>)
{
	var v_int_30: int, v_int_31: int := 12, 27;
	for v_int_29 := v_int_30 to v_int_31 
		invariant (v_int_31 - v_int_29 >= 0)
	{
		return [];
	}
	return [6, 0, 26];
}

method m_method_4(p_m_method_4_1: int) returns (ret_1: char)
	requires ((p_m_method_4_1 == 20));
	ensures (((p_m_method_4_1 == 20)) ==> ((ret_1 == 'e')));
{
	print "p_m_method_4_1", " ", p_m_method_4_1, "\n";
	return (if (true) then ('e') else ('P'));
}

method m_method_3(p_m_method_3_1: DT_1<set<int>, array<real>>, p_m_method_3_2: bool, p_m_method_3_3: map<bool, int>, p_m_method_3_4: real) returns (ret_1: real)
	requires ((p_m_method_3_1.DT_1_1? && ((p_m_method_3_1 == DT_1_1))) && (p_m_method_3_3 == map[false := 16, true := 2]) && (p_m_method_3_2 == false) && (-5.38 < p_m_method_3_4 < -5.18));
	ensures (((p_m_method_3_1.DT_1_1? && ((p_m_method_3_1 == DT_1_1))) && (p_m_method_3_3 == map[false := 16, true := 2]) && (p_m_method_3_2 == false) && (-5.38 < p_m_method_3_4 < -5.18)) ==> ((-26.10 < ret_1 < -25.90)));
{
	var v_bool_bool_1: (bool, bool) := (false, false);
	var v_map_1: map<int, (bool, bool)>, v_map_2: map<int, multiset<real>> := map[22 := v_bool_bool_1], map[8 := multiset{}, -21 := multiset{-3.07, -11.24, 20.05, -15.71}, 22 := multiset({-5.27, 16.26, 9.96}), 26 := multiset({}), 1 := multiset{}];
	if true {
		var v_bool_bool_11: (bool, bool) := (false, false);
		print "v_bool_bool_1.1", " ", v_bool_bool_1.1, " ", "v_bool_bool_1.0", " ", v_bool_bool_1.0, " ", "v_bool_bool_1", " ", v_bool_bool_1, " ", "p_m_method_3_2", " ", p_m_method_3_2, " ", "v_map_1", " ", (v_map_1 == map[22 := v_bool_bool_11]), " ", "p_m_method_3_1", " ", p_m_method_3_1, " ", "p_m_method_3_4", " ", (p_m_method_3_4 == -5.28), " ", "p_m_method_3_3", " ", (p_m_method_3_3 == map[false := 16, true := 2]), " ", "v_map_2", " ", (v_map_2 == map[1 := multiset{}, -21 := multiset{-11.24, 20.05, -15.71, -3.07}, 22 := multiset{16.26, 9.96, -5.27}, 8 := multiset{}, 26 := multiset{}]), "\n";
		return -26.00;
	} else {
		assert true;
		expect true;
		match 28 {
			case _ => {
				return -15.66;
			}
			
		}
		
		var v_int_bool_bool_1: (int, bool, bool) := (0, true, false);
		var v_bool_real_1: (bool, real) := (true, -0.53);
		var v_real_bool_1: (real, bool) := (-1.73, true);
		var v_int_bool_bool_bool_real_real_bool_1: ((int, bool, bool), (bool, real), (real, bool)) := (v_int_bool_bool_1, v_bool_real_1, v_real_bool_1);
		var v_int_bool_bool_bool_real_real_bool_2: ((int, bool, bool), (bool, real), (real, bool)), v_int_14: int := v_int_bool_bool_bool_real_real_bool_1, 23;
		var v_int_15: int, v_int_16: int := 7, -1;
		if false {
			return 5.95;
		} else {
			return -20.45;
		}
	}
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

method m_method_2(p_m_method_2_1: int, p_m_method_2_2: real, p_m_method_2_3: (bool, bool), p_m_method_2_4: (int, bool, real)) returns (ret_1: int)
	requires ((-26.10 < p_m_method_2_2 < -25.90) && (p_m_method_2_1 == 4) && ((p_m_method_2_4).0 == 25) && ((p_m_method_2_4).1 == true) && (-28.13 < (p_m_method_2_4).2 < -27.93) && ((p_m_method_2_3).0 == true) && ((p_m_method_2_3).1 == true));
	ensures (((-26.10 < p_m_method_2_2 < -25.90) && (p_m_method_2_1 == 4) && ((p_m_method_2_4).0 == 25) && ((p_m_method_2_4).1 == true) && (-28.13 < (p_m_method_2_4).2 < -27.93) && ((p_m_method_2_3).0 == true) && ((p_m_method_2_3).1 == true)) ==> ((ret_1 == 25)));
{
	var v_int_bool_real_12: (int, bool, real) := (25, true, -28.03);
	print "p_m_method_2_1", " ", p_m_method_2_1, " ", "p_m_method_2_3.0", " ", p_m_method_2_3.0, " ", "p_m_method_2_3.1", " ", p_m_method_2_3.1, " ", "p_m_method_2_4.0", " ", p_m_method_2_4.0, " ", "p_m_method_2_4.1", " ", p_m_method_2_4.1, " ", "p_m_method_2_4.2", " ", (p_m_method_2_4.2 == -28.03), " ", "p_m_method_2_3", " ", p_m_method_2_3, " ", "p_m_method_2_2", " ", (p_m_method_2_2 == -26.00), " ", "p_m_method_2_4", " ", (p_m_method_2_4 == v_int_bool_real_12), "\n";
	return p_m_method_2_4.0;
}

method m_method_1(p_m_method_1_1: char) returns (ret_1: bool)
	requires ((p_m_method_1_1 == 'e')) || ((p_m_method_1_1 == 'S'));
	ensures (((p_m_method_1_1 == 'e')) ==> ((ret_1 == true))) && (((p_m_method_1_1 == 'S')) ==> ((ret_1 == true)));
{
	var v_DT_1_1_1: DT_1<set<int>, array<real>> := DT_1_1;
	var v_int_9: int, v_DT_1_1_2: DT_1<set<int>, array<real>> := 18, v_DT_1_1_1;
	var v_int_11: int, v_int_12: int := 10, 2;
	for v_int_10 := v_int_11 downto v_int_12 
		invariant (v_int_10 - v_int_12 >= 0)
	{
		print "v_int_10", " ", v_int_10, " ", "p_m_method_1_1", " ", (p_m_method_1_1 == 'S'), " ", "v_DT_1_1_2", " ", v_DT_1_1_2, " ", "v_int_9", " ", v_int_9, " ", "v_DT_1_1_1", " ", v_DT_1_1_1, "\n";
		return true;
	}
	return false;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	if !((match false {
		case false => false
		case _ => (multiset{'R', 'A', 'P'} !! multiset({'b'}))
	})) {
		var v_int_7: int := (4 + (0 * 7));
		var v_char_1: char := 'S';
		var v_bool_1: bool := m_method_1(v_char_1);
		var v_seq_3: seq<map<bool, int>> := [map[false := 24, true := 29], map[true := 6], map[true := 4]];
		var v_int_13: int := 23;
		var v_seq_63: seq<map<bool, int>> := v_seq_3;
		var v_int_127: int := v_int_13;
		var v_int_128: int := safe_index_seq(v_seq_63, v_int_127);
		v_int_13 := v_int_128;
		var v_map_5: map<bool, int> := (if (v_bool_1) then ((if ((|v_seq_3| > 0)) then (v_seq_3[v_int_13]) else (map[false := 20]))) else ((if (true) then (map[true := 17, false := 12, false := 26, false := 20, true := 10]) else (map[true := 19]))));
		var v_bool_3: bool := v_bool_1;
		var v_int_19: int := v_int_7;
		var v_DT_1_1_3: DT_1<set<int>, array<real>> := DT_1_1;
		var v_DT_1_1_4: DT_1<set<int>, array<real>> := v_DT_1_1_3;
		var v_bool_2: bool := false;
		var v_map_3: map<bool, int> := map[false := 16, true := 2];
		var v_real_1: real := -5.28;
		var v_real_2: real := m_method_3(v_DT_1_1_4, v_bool_2, v_map_3, v_real_1);
		var v_real_3: real := v_real_2;
		var v_bool_bool_2: (bool, bool) := (true, true);
		var v_bool_bool_3: (bool, bool) := (true, true);
		var v_bool_bool_4: (bool, bool) := (false, true);
		var v_bool_bool_5: (bool, bool) := (true, true);
		var v_seq_4: seq<(bool, bool)> := [v_bool_bool_2, v_bool_bool_3, v_bool_bool_4, v_bool_bool_5];
		var v_int_17: int := 16;
		var v_seq_64: seq<(bool, bool)> := v_seq_4;
		var v_int_129: int := v_int_17;
		var v_int_130: int := safe_index_seq(v_seq_64, v_int_129);
		v_int_17 := v_int_130;
		var v_bool_bool_6: (bool, bool) := (true, true);
		var v_bool_bool_7: (bool, bool) := (if ((|v_seq_4| > 0)) then (v_seq_4[v_int_17]) else (v_bool_bool_6));
		var v_int_bool_real_1: (int, bool, real) := (15, true, 2.42);
		var v_map_4: map<int, (int, bool, real)> := map[6 := v_int_bool_real_1];
		var v_int_18: int := 1;
		var v_int_bool_real_2: (int, bool, real) := (25, true, -28.03);
		var v_int_bool_real_3: (int, bool, real) := (if ((v_int_18 in v_map_4)) then (v_map_4[v_int_18]) else (v_int_bool_real_2));
		var v_int_20: int := m_method_2(v_int_19, v_real_3, v_bool_bool_7, v_int_bool_real_3);
		var v_int_8: int := (if ((v_bool_3 in v_map_5)) then (v_map_5[v_bool_3]) else (v_int_20));
		while (v_int_7 < v_int_8) 
			decreases v_int_8 - v_int_7;
			invariant (v_int_7 <= v_int_8) && ((((v_int_7 == 4)) ==> ((((v_int_18 == 1))))));
		{
			v_int_7 := (v_int_7 + 1);
			if v_bool_bool_2.0 {
				var v_int_bool_real_13: (int, bool, real) := (25, true, -28.03);
				assert ((v_bool_1 == true) && (v_real_1 == -5.28) && (v_int_bool_real_3 == v_int_bool_real_13) && (v_int_18 == 1));
				expect ((v_bool_1 == true) && (v_real_1 == -5.28) && (v_int_bool_real_3 == v_int_bool_real_13) && (v_int_18 == 1));
				var v_seq_5: seq<int> := (([28] + [7, 14]) + ([27, 25] + [29, 12]));
				var v_map_6: map<int, int> := map[24 := 6, -7 := 2, 22 := 26];
				var v_int_21: int := 5;
				var v_int_22: int := ((if ((v_int_21 in v_map_6)) then (v_map_6[v_int_21]) else (0)) % v_int_bool_real_1.0);
				var v_seq_6: seq<int> := [24];
				var v_seq_65: seq<int> := v_seq_6;
				var v_int_133: int := 28;
				var v_int_134: int := -15;
				var v_int_135: int, v_int_136: int := safe_subsequence(v_seq_65, v_int_133, v_int_134);
				var v_int_131: int, v_int_132: int := v_int_135, v_int_136;
				var v_seq_7: seq<int> := (if ((|v_seq_6| > 0)) then (v_seq_6[v_int_131..v_int_132]) else (v_seq_6));
				var v_int_23: int := 5;
				var v_int_24: int := 28;
				var v_int_25: int := safe_division(v_int_23, v_int_24);
				var v_int_26: int := v_int_25;
				var v_map_7: map<int, int> := map[24 := 29, 8 := 3, 29 := 20, 25 := 7];
				var v_int_27: int := 16;
				v_int_18, v_int_22 := v_int_7, (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_22]) else ((if ((|v_seq_7| > 0)) then (v_seq_7[v_int_26]) else ((if ((v_int_27 in v_map_7)) then (v_map_7[v_int_27]) else (25))))));
				var v_int_28: int := (match 19 {
					case 28 => 22
					case _ => 20
				});
				var v_char_2: char := m_method_4(v_int_28);
				var v_char_3: char := v_char_2;
				var v_bool_4: bool := m_method_1(v_char_3);
				if v_bool_4 {
					var v_int_bool_real_14: (int, bool, real) := (15, true, 2.42);
					var v_int_bool_real_15: (int, bool, real) := (25, true, -28.03);
					var v_int_bool_real_16: (int, bool, real) := (15, true, 2.42);
					var v_int_bool_real_17: (int, bool, real) := (25, true, -28.03);
					print "v_map_7", " ", (v_map_7 == map[24 := 29, 8 := 3, 25 := 7, 29 := 20]), " ", "v_char_3", " ", (v_char_3 == 'e'), " ", "v_map_6", " ", (v_map_6 == map[-7 := 2, 22 := 26, 24 := 6]), " ", "v_char_2", " ", (v_char_2 == 'e'), " ", "v_int_18", " ", v_int_18, " ", "v_bool_4", " ", v_bool_4, " ", "v_int_24", " ", v_int_24, " ", "v_int_23", " ", v_int_23, " ", "v_seq_7", " ", v_seq_7, " ", "v_int_22", " ", v_int_22, " ", "v_seq_6", " ", v_seq_6, " ", "v_int_21", " ", v_int_21, " ", "v_seq_5", " ", v_seq_5, " ", "v_int_28", " ", v_int_28, " ", "v_int_27", " ", v_int_27, " ", "v_int_26", " ", v_int_26, " ", "v_int_25", " ", v_int_25, " ", "v_bool_1", " ", v_bool_1, " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_DT_1_1_3", " ", v_DT_1_1_3, " ", "v_DT_1_1_4", " ", v_DT_1_1_4, " ", "v_int_bool_real_1.2", " ", (v_int_bool_real_1.2 == 2.42), " ", "v_int_bool_real_2.1", " ", v_int_bool_real_2.1, " ", "v_int_bool_real_2.2", " ", (v_int_bool_real_2.2 == -28.03), " ", "v_int_19", " ", v_int_19, " ", "v_int_18", " ", v_int_18, " ", "v_bool_bool_5", " ", v_bool_bool_5, " ", "v_bool_bool_6", " ", v_bool_bool_6, " ", "v_bool_bool_7", " ", v_bool_bool_7, " ", "v_bool_bool_2", " ", v_bool_bool_2, " ", "v_bool_bool_3", " ", v_bool_bool_3, " ", "v_int_bool_real_1.0", " ", v_int_bool_real_1.0, " ", "v_bool_bool_4", " ", v_bool_bool_4, " ", "v_int_bool_real_1.1", " ", v_int_bool_real_1.1, " ", "v_int_bool_real_2.0", " ", v_int_bool_real_2.0, " ", "v_int_20", " ", v_int_20, " ", "v_char_1", " ", (v_char_1 == 'S'), " ", "v_map_5", " ", (v_map_5 == map[false := 24, true := 29]), " ", "v_map_4", " ", (v_map_4 == map[6 := v_int_bool_real_14]), " ", "v_int_bool_real_2", " ", (v_int_bool_real_2 == v_int_bool_real_15), " ", "v_int_bool_real_1", " ", (v_int_bool_real_1 == v_int_bool_real_16), " ", "v_int_bool_real_3", " ", (v_int_bool_real_3 == v_int_bool_real_17), " ", "v_int_8", " ", v_int_8, " ", "v_int_7", " ", v_int_7, " ", "v_bool_bool_6.1", " ", v_bool_bool_6.1, " ", "v_map_3", " ", (v_map_3 == map[false := 16, true := 2]), " ", "v_int_13", " ", v_int_13, " ", "v_bool_bool_2.0", " ", v_bool_bool_2.0, " ", "v_bool_bool_3.1", " ", v_bool_bool_3.1, " ", "v_bool_bool_4.0", " ", v_bool_bool_4.0, " ", "v_seq_4", " ", v_seq_4, " ", "v_int_17", " ", v_int_17, " ", "v_seq_3", " ", (v_seq_3 == [map[false := 24, true := 29], map[true := 6], map[true := 4]]), " ", "v_bool_bool_2.1", " ", v_bool_bool_2.1, " ", "v_bool_bool_3.0", " ", v_bool_bool_3.0, " ", "v_bool_bool_5.1", " ", v_bool_bool_5.1, " ", "v_bool_bool_6.0", " ", v_bool_bool_6.0, " ", "v_bool_bool_4.1", " ", v_bool_bool_4.1, " ", "v_bool_bool_5.0", " ", v_bool_bool_5.0, " ", "v_real_1", " ", (v_real_1 == -5.28), " ", "v_real_2", " ", (v_real_2 == -26.00), " ", "v_real_3", " ", (v_real_3 == -26.00), "\n";
					return ;
				} else {
					return ;
				}
			} else {
				break;
			}
		}
	}
	var v_int_32: int := 4;
	var v_int_33: int := 3;
	var v_int_34: int := 8;
	var v_seq_8: seq<int> := m_method_5(v_int_32, v_int_33, v_int_34);
	var v_map_8: map<int, int> := map[-1 := 28, 5 := 26, 5 := 6, 2 := 5, 14 := 1];
	var v_int_35: int := 24;
	v_int_34 := (|v_seq_8| % (v_int_32 + (if ((v_int_35 in v_map_8)) then (v_map_8[v_int_35]) else (4))));
	var v_int_36: int := 9;
	var v_int_37: int := 16;
	var v_int_38: int := safe_division(v_int_36, v_int_37);
	var v_int_39: int := v_int_38;
	var v_int_40: int := (if (true) then (1) else (17));
	var v_map_10: map<bool, int> := map[true := 7, true := 19];
	var v_bool_6: bool := false;
	var v_int_41: int := (if ((v_bool_6 in v_map_10)) then (v_map_10[v_bool_6]) else (26));
	var v_int_42: int := (match false {
		case _ => 1
	});
	var v_map_11: map<int, bool> := m_method_6(v_int_39, v_int_40, v_int_41, v_int_42);
	var v_map_12: map<int, bool> := v_map_11;
	var v_int_43: int := (if (false) then (4) else (14));
	var v_int_44: int := v_int_33;
	var v_int_45: int := safe_modulus(v_int_43, v_int_44);
	var v_int_46: int := v_int_45;
	if (if ((v_int_46 in v_map_12)) then (v_map_12[v_int_46]) else (v_bool_6)) {
		var v_map_13: map<bool, char> := map[true := 'U', false := 'B', true := 'R', false := 't'];
		var v_bool_7: bool := true;
		var v_seq_9: seq<char> := ['v'];
		var v_int_47: int := 4;
		var v_char_4: char := (match true {
			case _ => (if ((|v_seq_9| > 0)) then (v_seq_9[v_int_47]) else ('N'))
		});
		var v_bool_8: bool := m_method_1(v_char_4);
		match v_bool_8 {
			case _ => {
				var v_map_28: map<int, map<int, bool>> := map[2 := map[13 := false, -13 := true, 26 := true], -10 := map[27 := false, 13 := true, 17 := true, 24 := false, 13 := false], 15 := map[2 := false, 2 := false, 1 := false, 4 := true, 8 := true], 20 := map[6 := false, 4 := false, -23 := true, 25 := true, 17 := true]];
				var v_int_86: int := 25;
				var v_map_30: map<int, bool> := (match 13 {
					case _ => (if ((v_int_86 in v_map_28)) then (v_map_28[v_int_86]) else (map[26 := false, 5 := false]))
				});
				var v_map_29: map<seq<int>, real> := map[[] := 13.02, [-12, 18, 20] := 23.08, [7, 16] := 29.19, [27, -29] := 4.22, [9, 2, 21] := 22.06];
				var v_seq_35: seq<int> := [16, 17];
				var v_int_87: int := ((if ((v_seq_35 in v_map_29)) then (v_map_29[v_seq_35]) else (-6.68))).Floor;
				if (if ((v_int_87 in v_map_30)) then (v_map_30[v_int_87]) else (v_bool_6)) {
					
				}
				var v_seq_36: seq<real> := [9.82, 10.20];
				var v_int_88: int := -14;
				var v_seq_37: seq<real> := [-7.50, -26.72];
				var v_int_89: int := 5;
				v_int_45 := ((match 15 {
					case _ => (if (false) then (-11.41) else (4.89))
				})).Floor;
				var v_int_90: int := (v_int_43 - ((if (false) then (17) else (13)) - (if (false) then (1) else (29))));
				var v_seq_38: seq<map<(array<real>, map<real, real>), int>> := [];
				var v_int_92: int := 28;
				var v_array_11: array<real> := new real[5] [-15.68, -23.26, -23.85, -21.52, -27.43];
				var v_array_map_1: (array<real>, map<real, real>) := (v_array_11, map[2.16 := -27.83, 17.69 := 4.08]);
				var v_array_12: array<real> := new real[3] [-22.10, -22.36, -5.81];
				var v_array_map_2: (array<real>, map<real, real>) := (v_array_12, map[-8.68 := -15.52, -26.33 := -23.83, -21.31 := -12.40, 4.94 := 24.15, -0.48 := -8.80]);
				var v_array_13: array<real> := new real[3] [27.05, -16.19, 11.20];
				var v_array_map_3: (array<real>, map<real, real>) := (v_array_13, map[11.78 := -16.44]);
				var v_array_14: array<real> := new real[3] [19.00, 25.05, -3.47];
				var v_array_map_4: (array<real>, map<real, real>) := (v_array_14, map[29.77 := 24.80]);
				var v_array_15: array<real> := new real[5] [0.90, 2.57, 4.06, 27.73, 9.73];
				var v_array_map_5: (array<real>, map<real, real>) := (v_array_15, map[-27.39 := -22.46, 21.38 := 0.66, -23.16 := -0.52]);
				var v_map_31: map<bool, (array<real>, map<real, real>)> := map[false := v_array_map_3, false := v_array_map_4, false := v_array_map_5];
				var v_bool_16: bool := true;
				var v_array_16: array<real> := new real[5] [-21.55, 27.20, -21.63, -5.01, -27.49];
				var v_array_map_6: (array<real>, map<real, real>) := (v_array_16, map[5.89 := -13.80, 0.46 := -16.08, -0.86 := 28.42, -16.91 := -19.49]);
				var v_map_34: map<(array<real>, map<real, real>), int> := (if ((|v_seq_38| > 0)) then (v_seq_38[v_int_92]) else (map[v_array_map_1 := 27, v_array_map_2 := 21]))[(if ((v_bool_16 in v_map_31)) then (v_map_31[v_bool_16]) else (v_array_map_6)) := (if (false) then (2) else (0))];
				var v_array_17: array<int> := new int[5] [-14, 29, 4, 10, 14];
				var v_array_18: array<real> := new real[5] [23.22, 1.94, 28.16, -20.31, -22.49];
				var v_array_map_7: (array<real>, map<real, real>) := (v_array_18, map[20.38 := -25.65]);
				var v_array_19: array<int> := new int[3] [18, 13, 11];
				var v_array_20: array<real> := new real[5] [29.01, -7.59, -14.59, 22.72, 28.77];
				var v_array_map_8: (array<real>, map<real, real>) := (v_array_20, map[-26.89 := 9.47, -24.31 := -16.97, 1.60 := -14.75, -24.98 := -21.35, -1.02 := 20.05]);
				var v_array_21: array<int> := new int[4] [12, 6, 16, 9];
				var v_array_22: array<real> := new real[4] [8.61, -25.90, 13.90, -16.49];
				var v_array_map_9: (array<real>, map<real, real>) := (v_array_22, map[-16.26 := -19.56, 14.02 := 16.33]);
				var v_array_23: array<int> := new int[3] [17, 14, 9];
				var v_array_24: array<real> := new real[5] [-5.22, -8.57, 10.47, 12.54, 9.06];
				var v_array_map_10: (array<real>, map<real, real>) := (v_array_24, map[-24.89 := 3.51, 8.23 := -19.16, -16.81 := -21.68]);
				var v_array_25: array<int> := new int[5] [7, 19, 23, 7, 20];
				var v_array_26: array<real> := new real[3] [-9.21, -22.88, -16.19];
				var v_array_map_11: (array<real>, map<real, real>) := (v_array_26, map[7.01 := -23.59, 19.31 := 4.90]);
				var v_array_27: array<int> := new int[4] [12, 22, 10, -25];
				var v_array_28: array<real> := new real[3] [-15.83, -19.92, -21.82];
				var v_array_map_12: (array<real>, map<real, real>) := (v_array_28, map[22.16 := -24.41, -24.92 := -23.54]);
				var v_array_29: array<int> := new int[5] [6, 14, 8, 27, 23];
				var v_array_30: array<real> := new real[3] [-25.45, 17.40, -1.29];
				var v_array_map_13: (array<real>, map<real, real>) := (v_array_30, map[16.36 := -27.82, 24.53 := -19.73, 15.68 := -7.22, -15.11 := -11.09, 18.24 := 23.88]);
				var v_map_32: map<array<int>, (array<real>, map<real, real>)> := (if (true) then (map[v_array_17 := v_array_map_7, v_array_19 := v_array_map_8, v_array_21 := v_array_map_9, v_array_23 := v_array_map_10, v_array_25 := v_array_map_11]) else (map[v_array_27 := v_array_map_12, v_array_29 := v_array_map_13]));
				var v_array_33: array<int> := v_array_17;
				var v_array_31: array<real> := new real[5];
				v_array_31[0] := -19.52;
				v_array_31[1] := -25.61;
				v_array_31[2] := 5.81;
				v_array_31[3] := -10.40;
				v_array_31[4] := 13.61;
				var v_array_map_14: (array<real>, map<real, real>) := (v_array_31, map[0.27 := 4.26, -10.77 := 16.24, 29.81 := 12.73, -29.73 := 3.56, -17.15 := 3.02]);
				var v_array_32: array<real> := new real[4] [28.06, -24.02, -22.21, 9.45];
				var v_array_map_15: (array<real>, map<real, real>) := (v_array_32, map[-27.06 := -13.88, -28.68 := -14.42, 5.81 := 7.46, 7.24 := -1.86]);
				var v_array_map_16: (array<real>, map<real, real>) := (if ((v_array_33 in v_map_32)) then (v_map_32[v_array_33]) else ((if (true) then (v_array_map_14) else (v_array_map_15))));
				var v_array_34: array<multiset<real>> := new multiset<real>[3] [multiset{}, multiset{29.36, -9.44}, multiset{20.46, 21.12, 9.09}];
				var v_array_35: array<multiset<real>> := new multiset<real>[3] [multiset{-28.91}, multiset{20.71, 13.28}, multiset({22.38, -21.03, -10.90})];
				var v_array_36: array<multiset<real>> := new multiset<real>[5] [multiset({-16.85, 21.60, -27.03}), multiset{-17.11, 29.92}, multiset{-27.10, -27.23}, multiset{}, multiset{}];
				var v_array_37: array<multiset<real>> := new multiset<real>[4] [multiset({24.48, -12.00, 16.94, -17.63}), multiset({-27.16, -6.20, -5.69, -22.62}), multiset({2.39, 8.81, 14.75, 20.08}), multiset{-28.58}];
				var v_array_38: array<multiset<real>> := new multiset<real>[4] [multiset({15.09, 16.66, 10.84}), multiset{}, multiset{17.43, 8.50, 20.75}, multiset{-9.68, 9.56, 29.49}];
				var v_map_33: map<array<multiset<real>>, int> := (match true {
					case _ => map[v_array_35 := 20, v_array_36 := 16, v_array_37 := 27, v_array_38 := 15]
				});
				var v_array_39: array<multiset<real>> := new multiset<real>[4] [multiset{24.34}, multiset{-16.41, -6.71, -18.95, -20.73}, multiset({19.10, 2.44}), multiset{28.29, -2.72, -24.99}];
				var v_array_40: array<multiset<real>> := new multiset<real>[3] [multiset{5.25, -24.71, 20.17}, multiset{24.07, 22.94, -8.83}, multiset({22.93, -7.66})];
				var v_array_41: array<multiset<real>> := new multiset<real>[4] [multiset({1.63}), multiset({-3.89, 24.38, 19.65, 19.26}), multiset({18.82, 10.98}), multiset{-0.59}];
				var v_array_42: array<multiset<real>> := (match 'g' {
					case _ => v_array_41
				});
				var v_seq_39: seq<int> := [9, 29];
				var v_int_93: int := 3;
				var v_int_91: int := (if ((v_array_map_16 in v_map_34)) then (v_map_34[v_array_map_16]) else ((if ((v_array_42 in v_map_33)) then (v_map_33[v_array_42]) else ((if ((|v_seq_39| > 0)) then (v_seq_39[v_int_93]) else (-12))))));
				while (v_int_90 < v_int_91) 
					decreases v_int_91 - v_int_90;
					invariant (v_int_90 <= v_int_91);
				{
					v_int_90 := (v_int_90 + 1);
					var v_array_43: array<bool> := new bool[4];
					v_array_43[0] := false;
					v_array_43[1] := true;
					v_array_43[2] := true;
					v_array_43[3] := false;
					var v_array_44: array<bool> := new bool[5] [true, true, false, false, false];
					var v_array_45: array<bool> := new bool[4] [false, true, true, false];
					var v_array_46: array<array<bool>> := new array<bool>[3] [v_array_43, v_array_44, v_array_45];
					var v_array_47: array<bool> := new bool[5] [true, true, true, false, false];
					var v_array_48: array<bool> := new bool[5] [false, false, true, false, true];
					var v_array_49: array<bool> := new bool[4] [false, true, true, false];
					var v_array_50: array<array<bool>> := new array<bool>[3] [v_array_47, v_array_48, v_array_49];
					var v_map_35: map<bool, seq<set<set<bool>>>> := map[false := [{{false}}, {{true}, {true, false}, {true, true, false, true}}, {}, {{true}, {}}], false := []];
					var v_bool_17: bool := true;
					var v_int_95: int, v_int_96: int := ((match 4 {
						case _ => (if (false) then (14) else (24))
					}) + v_array_19[1]), (v_array_23[0] + |(if ((v_bool_17 in v_map_35)) then (v_map_35[v_bool_17]) else ([]))|);
					for v_int_94 := v_int_95 to v_int_96 
						invariant (v_int_96 - v_int_94 >= 0)
					{
						
					}
					return ;
				}
				assert true;
				expect true;
				return ;
			}
			
		}
		
		var v_map_36: map<bool, real> := map[true := 10.39, false := 3.42, false := -19.46];
		var v_bool_18: bool := false;
		var v_seq_40: seq<real> := [-18.30];
		var v_int_97: int := 1;
		var v_array_51: array<int> := new int[4] [26, 17, 29, 19];
		var v_array_52: array<int> := new int[4] [14, 25, 5, 13];
		var v_array_53: array<int> := new int[3] [9, 14, 10];
		var v_array_54: array<int> := new int[4];
		v_array_54[0] := -22;
		v_array_54[1] := 27;
		v_array_54[2] := 1;
		v_array_54[3] := 28;
		var v_map_37: map<array<int>, real> := map[v_array_51 := -19.22, v_array_52 := 19.54, v_array_53 := -26.18][v_array_54 := -14.67];
		var v_array_55: array<int> := new int[5] [9, 8, 25, 13, 9];
		var v_array_56: array<int> := new int[3] [25, 2, 23];
		var v_array_57: array<int> := new int[4] [16, 22, -21, 11];
		var v_array_58: array<int> := new int[5] [10, 0, -23, 0, 16];
		var v_seq_41: seq<array<int>> := [v_array_55, v_array_56, v_array_57, v_array_58];
		var v_int_98: int := 10;
		var v_array_59: array<int> := new int[3];
		v_array_59[0] := 16;
		v_array_59[1] := -6;
		v_array_59[2] := 20;
		var v_array_60: array<int> := (if ((|v_seq_41| > 0)) then (v_seq_41[v_int_98]) else (v_array_59));
		var v_bool_bool_real_1: (bool, bool, real) := (false, true, 0.84);
		var v_int_bool_bool_2: (int, bool, bool) := (1, true, false);
		var v_bool_bool_real_int_bool_bool_map_1: ((bool, bool, real), (int, bool, bool), map<bool, int>) := (v_bool_bool_real_1, v_int_bool_bool_2, map[true := 6, false := 0, true := 19, false := 27, false := 22]);
		var v_bool_bool_real_2: (bool, bool, real) := (true, false, 5.40);
		var v_int_bool_bool_3: (int, bool, bool) := (28, false, false);
		var v_bool_bool_real_int_bool_bool_map_2: ((bool, bool, real), (int, bool, bool), map<bool, int>) := (v_bool_bool_real_2, v_int_bool_bool_3, map[false := -17, true := 22]);
		var v_bool_bool_real_3: (bool, bool, real) := (false, true, 18.05);
		var v_int_bool_bool_4: (int, bool, bool) := (10, true, true);
		var v_bool_bool_real_int_bool_bool_map_3: ((bool, bool, real), (int, bool, bool), map<bool, int>) := (v_bool_bool_real_3, v_int_bool_bool_4, map[true := 16, true := 9]);
		var v_map_38: map<((bool, bool, real), (int, bool, bool), map<bool, int>), real> := map[v_bool_bool_real_int_bool_bool_map_1 := -26.96, v_bool_bool_real_int_bool_bool_map_2 := 23.80, v_bool_bool_real_int_bool_bool_map_3 := -22.27];
		var v_bool_bool_real_4: (bool, bool, real) := (false, false, -24.25);
		var v_int_bool_bool_5: (int, bool, bool) := (13, true, true);
		var v_bool_bool_real_int_bool_bool_map_4: ((bool, bool, real), (int, bool, bool), map<bool, int>) := (v_bool_bool_real_4, v_int_bool_bool_5, map[true := 7, true := 24]);
		var v_bool_bool_real_int_bool_bool_map_5: ((bool, bool, real), (int, bool, bool), map<bool, int>) := v_bool_bool_real_int_bool_bool_map_4;
		var v_bool_bool_int_1: (bool, bool, int) := (false, true, 22);
		var v_bool_bool_int_multiset_1: ((bool, bool, int), multiset<int>) := (v_bool_bool_int_1, multiset{17, 16, 22, -16});
		var v_bool_bool_int_2: (bool, bool, int) := (true, true, 2);
		var v_bool_bool_int_multiset_2: ((bool, bool, int), multiset<int>) := (v_bool_bool_int_2, multiset{12});
		var v_seq_42: seq<bool> := [];
		var v_seq_43: seq<bool> := (if ((|v_seq_42| > 0)) then (v_seq_42[9..6]) else (v_seq_42));
		var v_int_99: int := (28 / 18);
		var v_map_39: map<int, map<set<int>, char>> := map[7 := map[{15, 29, 1, 15} := 'd', {5} := 'K', {28} := 'P', {4, 18, 22, 17} := 'x'], 5 := map[{13, 23, 14} := 'i'], -16 := map[{} := 'Y', {3, 8, 17} := 'l', {4, 7, 24} := 'f'], -14 := map[{21, 0} := 'b']];
		var v_int_100: int := 3;
		var v_map_41: map<set<int>, char> := (if ((if (true) then (true) else (false))) then ((if (false) then (map[{0} := 'P', {13, 14, -27} := 'V', {26, 4, 13, 16} := 'S', {11, 7} := 'Y']) else (map[{20, 29, 23} := 'F']))) else ((if ((v_int_100 in v_map_39)) then (v_map_39[v_int_100]) else (map[{0} := 'a', {} := 'w', {28} := 'r', {24, -12, 14, 4} := 'd']))));
		var v_map_40: map<set<bool>, set<int>> := map[{false, false, true} := {27}, {} := {5, 5, 0}];
		var v_set_1: set<bool> := {false, false};
		var v_set_2: set<int> := (if ((match -21.55 {
			case _ => false
		})) then ((if ((v_set_1 in v_map_40)) then (v_map_40[v_set_1]) else ({}))) else ((if (false) then ({28, 9, -28}) else ({}))));
		var v_int_101: int, v_real_5: real, v_bool_19: bool, v_bool_20: bool, v_char_5: char := v_int_40, (if (((match 'q' {
			case _ => false
		}) <== (true || false))) then ((if ((if (false) then (true) else (false))) then ((if ((v_bool_18 in v_map_36)) then (v_map_36[v_bool_18]) else (18.19))) else ((if ((|v_seq_40| > 0)) then (v_seq_40[v_int_97]) else (3.09))))) else ((if ((v_array_60 in v_map_37)) then (v_map_37[v_array_60]) else ((if (false) then (-20.59) else (26.56)))))), !(((if ((v_bool_bool_real_int_bool_bool_map_5 in v_map_38)) then (v_map_38[v_bool_bool_real_int_bool_bool_map_5]) else (14.29)) in map[13.85 := v_bool_bool_int_multiset_1][28.03 := v_bool_bool_int_multiset_2])), (if ((if (({[21, 8, 23, 10]} !! {[18, 8], []})) then (v_bool_bool_real_1.0) else ((match 'W' {
			case _ => true
		})))) then ((if ((|v_seq_43| > 0)) then (v_seq_43[v_int_99]) else ((match 25 {
			case _ => true
		})))) else (v_int_bool_bool_5.1)), (if ((v_set_2 in v_map_41)) then (v_map_41[v_set_2]) else (v_char_4));
		var v_seq_44: seq<int> := v_seq_8;
		var v_int_104: int := (if (true) then (18) else (9));
		var v_map_42: map<char, int> := map['j' := 23, 'e' := -22, 'M' := 4, 'j' := 27, 'c' := -28];
		var v_char_6: char := 'M';
		var v_seq_45: seq<int> := [];
		var v_seq_46: seq<int> := v_seq_45;
		var v_int_105: int := -27;
		var v_int_106: int := safe_index_seq(v_seq_46, v_int_105);
		var v_int_107: int := v_int_106;
		var v_seq_48: seq<int> := (if ((|v_seq_45| > 0)) then (v_seq_45[v_int_107 := -1]) else (v_seq_45));
		var v_seq_47: seq<int> := [2];
		var v_int_108: int := 7;
		var v_int_109: int := (if ((|v_seq_47| > 0)) then (v_seq_47[v_int_108]) else (11));
		var v_int_102: int := (if (v_int_bool_bool_2.2) then ((if ((|v_seq_44| > 0)) then (v_seq_44[v_int_104]) else ((if ((v_char_6 in v_map_42)) then (v_map_42[v_char_6]) else (0))))) else ((if ((|v_seq_48| > 0)) then (v_seq_48[v_int_109]) else ((if (false) then (25) else (-29))))));
		var v_int_103: int := ((match 't' {
			case _ => v_array_53[1]
		}) % ((3 / 1) * (match 's' {
			case _ => 29
		})));
		while (v_int_102 < v_int_103) 
			decreases v_int_103 - v_int_102;
			invariant (v_int_102 <= v_int_103);
		{
			v_int_102 := (v_int_102 + 1);
			assert true;
			expect true;
			var v_map_43: map<char, bool> := map['Z' := false]['n' := true];
			var v_seq_49: seq<char> := ['r', 'N', 'P'];
			var v_int_110: int := 16;
			var v_char_7: char := (if ((|v_seq_49| > 0)) then (v_seq_49[v_int_110]) else ('k'));
			var v_seq_50: seq<bool> := [true, true, false];
			var v_int_111: int := 0;
			var v_seq_51: seq<char> := ['M', 'x', 'g'];
			var v_seq_52: seq<char> := (if ((|v_seq_51| > 0)) then (v_seq_51[0..2]) else (v_seq_51));
			var v_int_112: int := v_array_58[4];
			match (if ((if ((v_char_7 in v_map_43)) then (v_map_43[v_char_7]) else ((if ((|v_seq_50| > 0)) then (v_seq_50[v_int_111]) else (false))))) then ((if ((|v_seq_52| > 0)) then (v_seq_52[v_int_112]) else ((match 'I' {
				case _ => 'M'
			})))) else (v_char_7)) {
				case _ => {
					break;
				}
				
			}
			
		}
	}
	return ;
}

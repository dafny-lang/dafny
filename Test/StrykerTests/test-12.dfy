// RUN: %dafny /compile:0 "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %dafny /noVerify /deleteCodeAfterRun:1 /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
method safe_min_max(p_safe_min_max_1: int, p_safe_min_max_2: int) returns (ret_1: int, ret_2: int)
	ensures ((p_safe_min_max_1 < p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_1) && (ret_2 == p_safe_min_max_2))) && ((p_safe_min_max_1 >= p_safe_min_max_2) ==> ((ret_1 <= ret_2) && (ret_1 == p_safe_min_max_2) && (ret_2 == p_safe_min_max_1)));
{
	return (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_1) else (p_safe_min_max_2)), (if ((p_safe_min_max_1 < p_safe_min_max_2)) then (p_safe_min_max_2) else (p_safe_min_max_1));
}

method m_method_7(p_m_method_7_1: char) returns (ret_1: char)
	requires ((p_m_method_7_1 == 'R')) || ((p_m_method_7_1 == 'n'));
	ensures (((p_m_method_7_1 == 'n')) ==> ((ret_1 == 'l'))) && (((p_m_method_7_1 == 'R')) ==> ((ret_1 == 'l')));
{
	print "p_m_method_7_1", " ", (p_m_method_7_1 == 'n'), "\n";
	return 'l';
}

method safe_modulus(p_safe_modulus_1: int, p_safe_modulus_2: int) returns (ret_1: int)
	ensures (p_safe_modulus_2 == 0 ==> ret_1 == p_safe_modulus_1) && (p_safe_modulus_2 != 0 ==> ret_1 == p_safe_modulus_1 % p_safe_modulus_2);
{
	return (if ((p_safe_modulus_2 != 0)) then ((p_safe_modulus_1 % p_safe_modulus_2)) else (p_safe_modulus_1));
}

method m_method_6(p_m_method_6_1: char, p_m_method_6_2: char, p_m_method_6_3: char, p_m_method_6_4: char) returns (ret_1: char)
	requires ((p_m_method_6_4 == 'b') && (p_m_method_6_3 == 'b') && (p_m_method_6_2 == 'l') && (p_m_method_6_1 == 'M'));
	ensures (((p_m_method_6_4 == 'b') && (p_m_method_6_3 == 'b') && (p_m_method_6_2 == 'l') && (p_m_method_6_1 == 'M')) ==> ((ret_1 == 'A')));
{
	var v_char_10: char := 'R';
	var v_char_11: char := m_method_7(v_char_10);
	v_char_10, v_char_11 := (if ((false <==> false)) then (v_char_11) else (p_m_method_6_4)), p_m_method_6_3;
	var v_map_4: map<char, seq<char>> := map['z' := [], 'r' := ['H'], 'i' := ['M'], 'w' := ['N']];
	var v_char_12: char := 'D';
	var v_seq_10: seq<char> := (if ((v_char_12 in v_map_4)) then (v_map_4[v_char_12]) else (['A', 'I']));
	var v_map_5: map<char, int> := map['Q' := 2, 'H' := 28, 's' := 27, 'y' := 6, 'l' := 17];
	var v_char_13: char := 'h';
	var v_int_45: int := (if ((v_char_13 in v_map_5)) then (v_map_5[v_char_13]) else (7));
	var v_seq_14: seq<char> := v_seq_10;
	var v_int_52: int := v_int_45;
	var v_int_53: int := safe_index_seq(v_seq_14, v_int_52);
	v_int_45 := v_int_53;
	print "v_map_5", " ", (v_map_5 == map['Q' := 2, 's' := 27, 'H' := 28, 'y' := 6, 'l' := 17]), " ", "v_map_4", " ", (v_map_4 == map['r' := ['H'], 'w' := ['N'], 'i' := ['M'], 'z' := []]), " ", "v_int_45", " ", v_int_45, " ", "v_seq_10", " ", (v_seq_10 == ['A', 'I']), " ", "v_char_13", " ", (v_char_13 == 'h'), " ", "v_char_12", " ", (v_char_12 == 'D'), " ", "v_char_11", " ", (v_char_11 == 'b'), " ", "p_m_method_6_3", " ", (p_m_method_6_3 == 'b'), " ", "v_char_10", " ", (v_char_10 == 'l'), " ", "p_m_method_6_2", " ", (p_m_method_6_2 == 'l'), " ", "p_m_method_6_4", " ", (p_m_method_6_4 == 'b'), " ", "p_m_method_6_1", " ", (p_m_method_6_1 == 'M'), "\n";
	return (if ((|v_seq_10| > 0)) then (v_seq_10[v_int_45]) else (p_m_method_6_3));
}

method m_method_5(p_m_method_5_1: int, p_m_method_5_2: int, p_m_method_5_3: int, p_m_method_5_4: int) returns (ret_1: seq<real>)
	requires ((p_m_method_5_4 == 11) && (p_m_method_5_1 == -6) && (p_m_method_5_3 == 24) && (p_m_method_5_2 == 0));
	ensures (((p_m_method_5_4 == 11) && (p_m_method_5_1 == -6) && (p_m_method_5_3 == 24) && (p_m_method_5_2 == 0)) ==> (|ret_1| == 3 && (-19.16 < ret_1[0] < -18.96) && (28.37 < ret_1[1] < 28.57) && (7.73 < ret_1[2] < 7.93)));
{
	var v_map_2: map<char, bool> := map['l' := false, 'c' := false];
	var v_char_1: char := 'R';
	if (if ((v_char_1 in v_map_2)) then (v_map_2[v_char_1]) else (false)) {
		return (match 'I' {
			case _ => [-0.08, -29.70, 22.14]
		});
	} else {
		if (match 'G' {
			case 'L' => false
			case _ => true
		}) {
			var v_char_2: char, v_char_3: char := v_char_1, v_char_1;
			var v_char_4: char, v_char_5: char, v_char_6: char, v_char_7: char := v_char_1, v_char_2, v_char_3, (match 'f' {
				case 'P' => 'U'
				case 'x' => 'r'
				case _ => 'N'
			});
			print "v_char_3", " ", (v_char_3 == 'R'), " ", "v_char_2", " ", (v_char_2 == 'R'), " ", "v_char_5", " ", (v_char_5 == 'R'), " ", "v_char_4", " ", (v_char_4 == 'R'), " ", "v_char_7", " ", (v_char_7 == 'N'), " ", "v_char_6", " ", (v_char_6 == 'R'), " ", "v_char_1", " ", (v_char_1 == 'R'), " ", "p_m_method_5_4", " ", p_m_method_5_4, " ", "p_m_method_5_3", " ", p_m_method_5_3, " ", "p_m_method_5_2", " ", p_m_method_5_2, " ", "p_m_method_5_1", " ", p_m_method_5_1, " ", "v_map_2", " ", (v_map_2 == map['c' := false, 'l' := false]), "\n";
			return ([-19.06, 28.47] + [7.83]);
		}
		return ([] + []);
	}
}

method m_method_4(p_m_method_4_1: int, p_m_method_4_2: int) returns (ret_1: int, ret_2: int, ret_3: int)
{
	return 15, -20, 21;
}

method m_method_3(p_m_method_3_1: int, p_m_method_3_2: int) returns (ret_1: int, ret_2: int, ret_3: int, ret_4: int)
{
	return 10, 16, 20, 14;
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

method m_method_2(p_m_method_2_1: int) returns (ret_1: bool)
	requires ((p_m_method_2_1 == -6));
	ensures (((p_m_method_2_1 == -6)) ==> ((ret_1 == true)));
{
	var v_int_15: int, v_int_16: int := 15, 7;
	for v_int_11 := v_int_15 downto v_int_16 
		invariant (v_int_11 - v_int_16 >= 0)
	{
		if true {
			print "v_int_11", " ", v_int_11, " ", "p_m_method_2_1", " ", p_m_method_2_1, "\n";
			return true;
		}
		var v_int_13: int, v_int_14: int := 11, 11;
		for v_int_12 := v_int_13 to v_int_14 
			invariant (v_int_14 - v_int_12 >= 0)
		{
			
		}
		return false;
	}
	match 14 {
		case _ => {
			var v_int_32: int := 16;
			if false {
				return false;
			} else {
				return false;
			}
		}
		
	}
	
}

method m_method_1(p_m_method_1_1: array<real>, p_m_method_1_2: seq<real>, p_m_method_1_3: bool, p_m_method_1_4: char) returns (ret_1: bool)
	requires (p_m_method_1_1.Length == 4 && (-19.85 < p_m_method_1_1[0] < -19.65) && (-2.51 < p_m_method_1_1[1] < -2.31) && (-19.91 < p_m_method_1_1[2] < -19.71) && (-10.90 < p_m_method_1_1[3] < -10.70) && (p_m_method_1_3 == false) && |p_m_method_1_2| == 3 && (-19.16 < p_m_method_1_2[0] < -18.96) && (28.37 < p_m_method_1_2[1] < 28.57) && (7.73 < p_m_method_1_2[2] < 7.93) && (p_m_method_1_4 == 'b'));
	ensures ((p_m_method_1_1.Length == 4 && (-19.85 < p_m_method_1_1[0] < -19.65) && (-2.51 < p_m_method_1_1[1] < -2.31) && (-19.91 < p_m_method_1_1[2] < -19.71) && (-10.90 < p_m_method_1_1[3] < -10.70) && (p_m_method_1_3 == false) && |p_m_method_1_2| == 3 && (-19.16 < p_m_method_1_2[0] < -18.96) && (28.37 < p_m_method_1_2[1] < 28.57) && (7.73 < p_m_method_1_2[2] < 7.93) && (p_m_method_1_4 == 'b')) ==> ((ret_1 == true)));
{
	if p_m_method_1_3 {
		var v_seq_3: seq<multiset<int>> := [multiset({19}), multiset{24, 1, 22, 23}];
		var v_int_7: int := 9;
		if ((match 18 {
			case _ => 5
		}) !in (if ((|v_seq_3| > 0)) then (v_seq_3[v_int_7]) else (multiset{}))) {
			assert true;
			expect true;
			var v_int_8: int, v_int_9: int := 23, 25;
		} else {
			var v_map_1: map<int, int> := map[12 := 4, 9 := 20, 6 := 18, 6 := 13, 5 := 8];
			var v_int_10: int := 27;
			return ((if ((v_int_10 in v_map_1)) then (v_map_1[v_int_10]) else (2)) in (map[16 := 14, 4 := 7, 4 := 4, 25 := -23]).Values);
		}
	}
	var v_int_33: int := -6;
	var v_bool_1: bool := m_method_2(v_int_33);
	if !(v_bool_1) {
		
	}
	print "v_bool_1", " ", v_bool_1, " ", "p_m_method_1_2", " ", (p_m_method_1_2 == [-19.06, 28.47, 7.83]), " ", "v_int_33", " ", v_int_33, " ", "p_m_method_1_1", " ", "p_m_method_1_1[2]", " ", (p_m_method_1_1[2] == -19.81), " ", "p_m_method_1_1[1]", " ", (p_m_method_1_1[1] == -2.41), " ", "p_m_method_1_1[0]", " ", (p_m_method_1_1[0] == -19.75), " ", "p_m_method_1_4", " ", (p_m_method_1_4 == 'b'), " ", "p_m_method_1_3", " ", p_m_method_1_3, "\n";
	return v_bool_1;
}

method safe_index_seq(p_safe_index_seq_1: seq, p_safe_index_seq_2: int) returns (ret_1: int)
	ensures ((0 <= p_safe_index_seq_2 < |p_safe_index_seq_1|) ==> (ret_1 == p_safe_index_seq_2)) && ((0 > p_safe_index_seq_2 || p_safe_index_seq_2 >= |p_safe_index_seq_1|) ==> (ret_1 == 0));
{
	return (if (((p_safe_index_seq_2 < |p_safe_index_seq_1|) && (0 <= p_safe_index_seq_2))) then (p_safe_index_seq_2) else (0));
}

method Main() returns ()
{
	var v_seq_4: seq<array<real>> := [];
	var v_int_34: int := 26;
	var v_array_1: array<real> := new real[4] [-19.75, -2.41, -19.81, -10.80];
	var v_array_2: array<real> := (if ((4 > 19)) then ((if ((|v_seq_4| > 0)) then (v_seq_4[v_int_34]) else (v_array_1))) else (v_array_1));
	var v_int_39: int := (match 'u' {
		case 'R' => 14
		case 'D' => 5
		case _ => -6
	});
	var v_int_35: int := 10;
	var v_int_36: int := 24;
	var v_int_37: int := safe_division(v_int_35, v_int_36);
	var v_int_40: int := v_int_37;
	var v_int_41: int := v_int_36;
	var v_seq_5: seq<int> := [11];
	var v_int_38: int := 23;
	var v_seq_11: seq<int> := v_seq_5;
	var v_int_46: int := v_int_38;
	var v_int_47: int := safe_index_seq(v_seq_11, v_int_46);
	v_int_38 := v_int_47;
	var v_int_42: int := (if ((|v_seq_5| > 0)) then (v_seq_5[v_int_38]) else (19));
	var v_seq_6: seq<real> := m_method_5(v_int_39, v_int_40, v_int_41, v_int_42);
	var v_seq_9: seq<real> := v_seq_6;
	var v_seq_7: seq<bool> := (match 'G' {
		case 'l' => [true]
		case _ => [false, false]
	});
	var v_int_43: int := (if (false) then (15) else (25));
	var v_seq_12: seq<bool> := v_seq_7;
	var v_int_48: int := v_int_43;
	var v_int_49: int := safe_index_seq(v_seq_12, v_int_48);
	v_int_43 := v_int_49;
	var v_bool_2: bool := (if ((|v_seq_7| > 0)) then (v_seq_7[v_int_43]) else ((['Q', 'I', 'w'] != ['z', 'm', 's'])));
	var v_map_3: map<char, char> := (map['S' := 'q', 'g' := 'M'] - {});
	var v_char_8: char := (match 'd' {
		case 'w' => 'R'
		case _ => 'M'
	});
	var v_seq_8: seq<char> := ['b', 'p', 'Z', 'J'];
	var v_int_44: int := 5;
	var v_seq_13: seq<char> := v_seq_8;
	var v_int_50: int := v_int_44;
	var v_int_51: int := safe_index_seq(v_seq_13, v_int_50);
	v_int_44 := v_int_51;
	var v_char_9: char := (if ((v_char_8 in v_map_3)) then (v_map_3[v_char_8]) else ((if ((|v_seq_8| > 0)) then (v_seq_8[v_int_44]) else ('G'))));
	var v_bool_3: bool := m_method_1(v_array_2, v_seq_9, v_bool_2, v_char_9);
	if v_bool_3 {
		var v_char_16: char := v_char_8;
		var v_char_14: char := 'n';
		var v_char_15: char := m_method_7(v_char_14);
		var v_char_17: char := (match 'n' {
			case 'Z' => (if (true) then ('F') else ('d'))
			case _ => v_char_15
		});
		var v_char_18: char := v_char_9;
		var v_char_19: char := v_char_9;
		var v_char_20: char := m_method_6(v_char_16, v_char_17, v_char_18, v_char_19);
		v_char_17, v_char_16, v_char_19, v_char_20 := v_char_9, v_char_9, v_char_20, v_char_18;
		print "v_char_18", " ", (v_char_18 == 'b'), " ", "v_char_17", " ", (v_char_17 == 'b'), " ", "v_char_16", " ", (v_char_16 == 'b'), " ", "v_char_20", " ", (v_char_20 == 'b'), " ", "v_char_19", " ", (v_char_19 == 'A'), " ", "v_bool_3", " ", v_bool_3, " ", "v_bool_2", " ", v_bool_2, " ", "v_int_44", " ", v_int_44, " ", "v_int_43", " ", v_int_43, " ", "v_array_1", " ", (v_array_1 == v_array_1), " ", "v_array_2", " ", (v_array_2 == v_array_1), " ", "v_array_1[2]", " ", (v_array_1[2] == -19.81), " ", "v_array_1[0]", " ", (v_array_1[0] == -19.75), " ", "v_int_42", " ", v_int_42, " ", "v_int_41", " ", v_int_41, " ", "v_int_40", " ", v_int_40, " ", "v_char_9", " ", (v_char_9 == 'b'), " ", "v_char_8", " ", (v_char_8 == 'M'), " ", "v_map_3", " ", (v_map_3 == map['S' := 'q', 'g' := 'M']), " ", "v_seq_9", " ", (v_seq_9 == [-19.06, 28.47, 7.83]), " ", "v_int_35", " ", v_int_35, " ", "v_seq_8", " ", (v_seq_8 == ['b', 'p', 'Z', 'J']), " ", "v_int_34", " ", v_int_34, " ", "v_seq_7", " ", v_seq_7, " ", "v_seq_6", " ", (v_seq_6 == [-19.06, 28.47, 7.83]), " ", "v_seq_5", " ", v_seq_5, " ", "v_seq_4", " ", (v_seq_4 == []), " ", "v_int_39", " ", v_int_39, " ", "v_int_38", " ", v_int_38, " ", "v_int_37", " ", v_int_37, " ", "v_int_36", " ", v_int_36, " ", "v_array_1[1]", " ", (v_array_1[1] == -2.41), " ", "v_array_1[3]", " ", (v_array_1[3] == -10.80), "\n";
		return ;
	} else {
		return ;
	}
}

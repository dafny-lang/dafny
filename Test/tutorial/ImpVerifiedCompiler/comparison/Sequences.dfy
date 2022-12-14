least predicate star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
	(conf1 == conf2) || (exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

lemma star_one_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
	requires R(conf1,conf2)
	ensures star(R,conf1,conf2)
{
}

lemma star_one<T(!new)>()
	ensures forall R: (T,T) -> bool :: forall conf1, conf2: T :: R(conf1,conf2) ==> star(R,conf1,conf2)
{
}

predicate Star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
  star(R, conf1, conf2)
}

least lemma star_trans_pre<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
	requires star(R,conf1,conf2)
	ensures  star(R,conf2,conf3) ==> star(R,conf1,conf3)
{
	if conf1 == conf2 {}
	else {
		var confi :| R(conf1, confi) && star(R,confi, conf2);
		assert star(R,confi,conf2);
		star_trans_pre(R,confi,conf2,conf3); 
	}
}

lemma star_trans_sequent<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
	requires star(R,conf1,conf2) 
	requires star(R,conf2,conf3)
	ensures star(R,conf1,conf3)
{
	star_trans_pre(R,conf1,conf2,conf3);
}

lemma star_trans<T(!new)>()
	ensures forall R: (T,T) -> bool :: forall conf1, conf2, conf3: T :: (star(R,conf1,conf2) && star(R,conf2,conf3)) ==> star(R,conf1,conf3)
{
	forall R, conf1, conf2, conf3: T ensures (star(R,conf1,conf2) && star(R,conf2,conf3)) ==> star(R,conf1,conf3) {
		if star(R,conf1,conf2) {
			star_trans_pre(R,conf1,conf2,conf3);
		}
	}
}

least predicate plus<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
	(exists conf_inter: T :: R(conf1, conf_inter) && star(R,conf_inter, conf2))
}

least predicate Plus<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T) {
	plus(R,conf1, conf2)
}

lemma plus_one<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
	requires R(conf1,conf2)
	ensures star(R,conf1,conf2)
{
}

lemma plus_star<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
	requires plus(R,conf1,conf2)
	ensures star(R,conf1,conf2)
{
	var conf1' :| R(conf1, conf1') && star(R,conf1', conf2);
	star_one_sequent(R,conf1,conf1');
	star_trans_sequent(R,conf1,conf1',conf2);
}

/* Missing plus_star_trans */

lemma star_plus_trans<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T, conf3: T)
	requires star(R,conf1,conf2)
	requires plus(R,conf2,conf3)
	ensures plus(R,conf1,conf3)
{
	if conf1 == conf2 {
	} else {
		var conf1' :| R(conf1, conf1') && star(R,conf1', conf2);
		var conf2' :| R(conf2, conf2') && star(R,conf2', conf3);
		star_one_sequent(R,conf2,conf2');
		star_trans_sequent(R,conf1',conf2,conf2');
		star_trans_sequent(R,conf1',conf2',conf3);
	}
}

/* Missing plus_right */

/* Missing irred */

predicate all_seq_inf<T(!new)>(R: (T,T) -> bool,conf: T) {
	forall conf2: T :: star(R,conf,conf2) ==> exists conf3: T :: R(conf2,conf3)
}

/* Missing infseq_with_function */

greatest predicate infseq<T(!new)>(R: (T,T) -> bool,conf: T) {
	exists confi: T :: R(conf,confi) && infseq(R,confi)
}

greatest predicate Inf<T(!new)>(R: (T,T) -> bool,conf: T) {
	infseq(R,conf)
}

/* Missing cycle_infseq */

least lemma star_inf_trans<T(!new)>(R: (T,T) -> bool, conf1: T, conf2: T)
	requires star(R,conf1,conf2)
	requires infseq(R,conf2)
	ensures infseq(R,conf1)
{
	if conf1 == conf2 {}
	else {
		var conf1' :| R(conf1, conf1') && star(R,conf1', conf2);
		star_inf_trans(R,conf1',conf2);
	}
}
	
greatest lemma infseq_if_all_seq_inf_pre<T(!new)>(R: (T,T) -> bool, conf: T)
	requires forall conf2: T :: star(R,conf,conf2) ==> exists conf3: T :: R(conf2,conf3)
	ensures infseq(R,conf)
{
	assert star(R,conf,conf);
	var B :| R(conf,B);
	assert R(conf,B);
	assert infseq(R,B) by { infseq_if_all_seq_inf_pre(R,B); }
}

lemma infseq_if_all_seq_inf<T(!new)>(R: (T,T) -> bool, conf: T)
	requires all_seq_inf(R,conf)
	ensures infseq(R,conf)
{
	infseq_if_all_seq_inf_pre(R,conf);
}

lemma infseq_coinduction_principle_ord<T(!new)>(k: ORDINAL, R: (T,T) -> bool, X: T -> bool, a : T)
	requires (forall a: T :: X(a) ==> exists b: T :: R(a,b) && X(b))
	requires X(a)
	ensures infseq#[k](R,a)
{
	if k.Offset == 0 {} else {
		var b :| R(a,b) && X(b);
		infseq_coinduction_principle_ord(k-1,R,X,b);
	}
}

predicate {:opaque} always_step<T(!new)>(R: (T,T) -> bool, X: T -> bool) {
	forall a: T :: X(a) ==> exists b: T :: R(a,b) && X(b)
}

greatest lemma infseq_coinduction_principle_pre<T(!new)>(R: (T,T) -> bool, X: T -> bool, a: T)
	requires always_step(R,X)
	ensures  X(a) ==> infseq(R,a)
{
	reveal always_step();
	forall a: T ensures X(a) ==> infseq(R,a) {
		if X(a) {
			var b :| R(a,b) && X(b);
			infseq_coinduction_principle_pre(R,X,a);
		}
	}
}

lemma infseq_coinduction_principle<T(!new)>(R: (T,T) -> bool, X: T -> bool, a : T)
	requires always_step(R,X)
	requires X(a)
	ensures infseq(R,a)
{
	reveal always_step();
	if X(a) {
		infseq_coinduction_principle_pre(R,X,a);
	}
	
}

predicate {:opaque} Y<T(!new)>(R: (T,T) -> bool, X: T -> bool, a: T) {
	exists b: T :: star(R,a,b) && X(b)
}

predicate {:opaque} always_steps<T(!new)>(R: (T,T) -> bool, X: T -> bool) {
	forall a: T :: X(a) ==> exists b: T :: plus(R,a, b) && X(b)
}

lemma infseq_coinduction_principle_2_pre_lift<T(!new)>(R: (T,T) -> bool, X: T -> bool)
	requires always_steps(R,X)
	ensures always_step(R,(a: T) => Y(R,X,a))
{
	reveal always_step();
	forall a: T ensures ((a: T) => Y(R,X,a))(a) ==> exists b: T :: R(a, b) && ((a: T) => Y(R,X,a))(b) {
		if ((a: T) => Y(R,X,a))(a) {
			reveal always_steps();
			var b :| plus(R,a, b) && X(b);
			var c :| R(a,c) && star(R,c,b);
		}
	}
}

lemma infseq_coinduction_principle_2<T(!new)>(R: (T,T) -> bool, X: T -> bool, a : T)
	requires H1: always_steps(R,X)
	requires H2: X(a)
	ensures infseq(R,a)
{

	assert Y(R,X,a) by {
		reveal H2;
		reveal Y();
	}

	assert always_step(R,(a: T) => Y(R,X,a)) by {
		reveal H1;
		infseq_coinduction_principle_2_pre_lift(R,X);
	}
	
	infseq_coinduction_principle(R,(a: T) => Y(R,X,a),a);
	
}

/* The tutorial continues from there */


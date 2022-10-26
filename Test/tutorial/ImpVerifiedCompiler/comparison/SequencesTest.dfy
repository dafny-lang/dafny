abstract module SEQUENCES {

	type T(!new)
	predicate R(x: T,y: T)
	
	least predicate star(conf1: T, conf2: T) {
		(conf1 == conf2) || (exists conf_inter: T :: R(conf1, conf_inter) && star(conf_inter, conf2))
	}

	predicate Star(conf1: T, conf2: T) {
		star(conf1, conf2)
	}

	lemma star_one_sequent(conf1: T, conf2: T)
		requires R(conf1,conf2)
		ensures star(conf1,conf2)
	{
	}

	lemma star_one()
		ensures forall R: (T,T) -> bool :: forall conf1, conf2: T :: R(conf1,conf2) ==> star(conf1,conf2)
	{
	}

	least lemma star_trans_pre(conf1: T, conf2: T, conf3: T)
		requires star(conf1,conf2)
		ensures  star(conf2,conf3) ==> star(conf1,conf3)
	{
		if conf1 == conf2 {}
		else {
			var confi :| R(conf1, confi) && star(confi, conf2);
			assert star(confi,conf2);
			star_trans_pre(confi,conf2,conf3); 
		}
	}

	lemma star_trans_sequent(conf1: T, conf2: T, conf3: T)
		requires star(conf1,conf2) 
		requires star(conf2,conf3)
		ensures star(conf1,conf3)
	{
		star_trans_pre(conf1,conf2,conf3);
	}

	lemma star_trans()
		ensures forall R: (T,T) -> bool :: forall conf1, conf2, conf3: T :: (star(conf1,conf2) && star(conf2,conf3)) ==> star(conf1,conf3)
	{
		forall conf1, conf2, conf3: T ensures (star(conf1,conf2) && star(conf2,conf3)) ==> star(conf1,conf3) {
			if star(conf1,conf2) {
				star_trans_pre(conf1,conf2,conf3);
			}
		}
	}

	lemma combine_reductions()
		ensures forall R: (T,T) -> bool :: forall conf1, conf2: T :: R(conf1,conf2) ==> star(conf1,conf2)
		ensures forall R: (T,T) -> bool :: forall conf1, conf2, conf3: T :: (star(conf1,conf2) && star(conf2,conf3)) ==> star(conf1,conf3)
	{
		star_one();
		star_trans();
	}

	least predicate plus(conf1: T, conf2: T) {
		(exists conf_inter: T :: R(conf1, conf_inter) && star(conf_inter, conf2))
	}

	least predicate Plus(conf1: T, conf2: T) {
		plus(conf1, conf2)
	}

	lemma plus_one(conf1: T, conf2: T)
		requires R(conf1,conf2)
		ensures star(conf1,conf2)
	{
	}

	lemma plus_star(conf1: T, conf2: T)
		requires plus(conf1,conf2)
		ensures star(conf1,conf2)
	{
		var conf1' :| R(conf1, conf1') && star(conf1', conf2);
		star_one_sequent(conf1,conf1');
		star_trans_sequent(conf1,conf1',conf2);
	}

	lemma star_plus_trans(conf1: T, conf2: T, conf3: T)
		requires star(conf1,conf2)
		requires plus(conf2,conf3)
		ensures plus(conf1,conf3)
	{
		if conf1 == conf2 {
		} else {
			var conf1' :| R(conf1, conf1') && star(conf1', conf2);
			var conf2' :| R(conf2, conf2') && star(conf2', conf3);
			star_one_sequent(conf2,conf2');
			star_trans_sequent(conf1',conf2,conf2');
			star_trans_sequent(conf1',conf2',conf3);
		}
	}


	predicate all_seq_inf(conf: T) {
		forall conf2: T :: star(conf,conf2) ==> exists conf3: T :: R(conf2,conf3)
	}

	greatest predicate inf(conf: T) {
		exists confi: T :: R(conf,confi) && inf(confi)
	}

	greatest predicate Inf(conf: T) {
		inf(conf)
	}

	least lemma star_inf_trans(conf1: T, conf2: T)
		requires star(conf1,conf2)
		requires inf(conf2)
		ensures inf(conf1)
	{
		if conf1 == conf2 {}
		else {
			var conf1' :| R(conf1, conf1') && star(conf1', conf2);
			star_inf_trans(conf1',conf2);
		}
	}
	
	greatest lemma infseq_if_all_seq_inf_pre(conf: T)
		requires forall conf2: T :: star(conf,conf2) ==> exists conf3: T :: R(conf2,conf3)
		ensures inf(conf)
	{
		assert star(conf,conf);
		var B :| R(conf,B);
		assert R(conf,B);
		assert inf(B) by { infseq_if_all_seq_inf_pre(B); }
	}

	lemma infseq_if_all_seq_inf(conf: T)
		requires all_seq_inf(conf)
		ensures inf(conf)
	{
		infseq_if_all_seq_inf_pre(conf);
	}

	lemma infseq_coinduction_principle_ord(k: ORDINAL, X: T -> bool, a : T)
		requires (forall a: T :: X(a) ==> exists b: T :: R(a,b) && X(b))
		requires X(a)
		ensures inf#[k](a)
	{
		if k.Offset == 0 {} else {
			var b :| R(a,b) && X(b);
			infseq_coinduction_principle_ord(k-1,X,b);
		}
	}

	predicate {:opaque} always_step(X: T -> bool) {
		forall a: T :: X(a) ==> exists b: T :: R(a,b) && X(b)
	}

	greatest lemma infseq_coinduction_principle_pre(X: T -> bool, a: T)
		requires always_step(X)
		ensures  X(a) ==> inf(a)
	{
		reveal always_step();
		forall a: T ensures X(a) ==> inf(a) {
			if X(a) {
				var b :| R(a,b) && X(b);
				infseq_coinduction_principle_pre(X,a);
			}
		}
	}

	lemma infseq_coinduction_principle(X: T -> bool, a : T)
		requires always_step(X)
		requires X(a)
		ensures inf(a)
	{
		reveal always_step();
		if X(a) {
			infseq_coinduction_principle_pre(X,a);
		}
		
	}

	predicate {:opaque} Y(X: T -> bool, a: T) {
		exists b: T :: star(a,b) && X(b)
	}

	predicate {:opaque} always_steps(X: T -> bool) {
		forall a: T :: X(a) ==> exists b: T :: plus(a, b) && X(b)
	}

	lemma infseq_coinduction_principle_2_pre_lift(X: T -> bool)
		requires always_steps(X)
		ensures always_step((a: T) => Y(X,a))
	{
		reveal always_step();
		forall a: T ensures ((a: T) => Y(X,a))(a) ==> exists b: T :: R(a, b) && ((a: T) => Y(X,a))(b) {
			if ((a: T) => Y(X,a))(a) {
				reveal always_steps();
				var b :| plus(a, b) && X(b);
				var c :| R(a,c) && star(c,b);
			}
		}
	}

	lemma infseq_coinduction_principle_2(X: T -> bool, a : T)
		requires H1: always_steps(X)
		requires H2: X(a)
		ensures inf(a)
	{

		assert Y(X,a) by {
			reveal H2;
			reveal Y();
		}

		assert always_step((a: T) => Y(X,a)) by {
			reveal H1;
			infseq_coinduction_principle_2_pre_lift(X);
		}
		
		infseq_coinduction_principle((a: T) => Y(X,a),a);
		
	}

}

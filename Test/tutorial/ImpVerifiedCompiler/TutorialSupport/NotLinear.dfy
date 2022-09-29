predicate A()
predicate B()

lemma premise()
	requires A()
	requires A()
	ensures B()

lemma not_linear_logic()
	requires A()
	ensures B()
{
	premise();
}

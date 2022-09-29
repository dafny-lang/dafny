type t
predicate P(x: t)
	
ghost const test1: bool := forall x: t :: P(x)

lemma proof_information_gone()
	ensures test1 == true || test1 == false
{
}

ghost const test2: bool := forall x: t :: P(x)

lemma proof_irrelevance()
	ensures test1 == test2
{
}
	

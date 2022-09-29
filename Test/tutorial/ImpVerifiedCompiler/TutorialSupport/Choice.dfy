type tin
type tout

predicate P(x: tin, y: tout)

function f(x: tin): tout
	requires forall x: tin :: exists y: tout :: P(x,y)
{
	var y :| P(x,y);
	y
}

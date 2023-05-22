// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type SendState = map<int, seq<int>>

ghost function UnAckedMessages(s:SendState) : set<int>
{
    set m,dst | dst in s && m in s[dst] :: m
}

ghost function UnAckedMessagesForDst(s:SendState, dst:int) : set<int>
    requires dst in s;
{
    set m | m in s[dst] :: m
}

ghost function UnAckedMessages3(s:SendState) : set<int>
{
    set m,dst | dst in s && m in UnAckedMessagesForDst(s, dst) :: m
}

ghost function SeqToSet<T>(s:seq<T>) : set<T>
{
    set i | i in s
}

ghost function UnAckedMessages4(s:SendState) : set<int>
{
		set m,dst | dst in s && m in SeqToSet(s[dst]) :: m
}

ghost function UnAckedLists(s:SendState) : set<seq<int>>
{
    set dst | dst in s :: s[dst]
}

ghost function UnAckedMessages5(s:SendState) : set<int>
{
    set m, list | list in UnAckedLists(s) && m in list :: m
}
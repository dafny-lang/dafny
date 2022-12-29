// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type SendState = map<int, seq<int>>

function UnAckedMessages(s:SendState) : set<int>
{
    set m,dst | dst in s && m in s[dst] :: m
}

function UnAckedMessagesForDst(s:SendState, dst:int) : set<int>
    requires dst in s;
{
    set m | m in s[dst] :: m
}

function UnAckedMessages3(s:SendState) : set<int>
{
    set m,dst | dst in s && m in UnAckedMessagesForDst(s, dst) :: m
}

function SeqToSet<T>(s:seq<T>) : set<T>
{
    set i | i in s
}

function UnAckedMessages4(s:SendState) : set<int>
{
		set m,dst | dst in s && m in SeqToSet(s[dst]) :: m
}

function UnAckedLists(s:SendState) : set<seq<int>>
{
    set dst | dst in s :: s[dst]
}

function UnAckedMessages5(s:SendState) : set<int>
{
    set m, list | list in UnAckedLists(s) && m in list :: m
}

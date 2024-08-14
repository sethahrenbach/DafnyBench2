predicate derangement(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> s[i] != i
}

predicate permutation(s: seq<nat>) {
    forall i :: 0 <= i < |s| ==> i in s
}

function multisetRange(n: nat): multiset<nat> {
    multiset(seq(n, i => i))
}

predicate distinct<A(==)>(s: seq<A>) {
    forall x,y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
}

method test() {
    var tests := [2,0,1];
    var tests2 := [0,1,2];
    var t4 := seq(3, i => i);
    var test3 := multisetRange(3);
    assert !derangement(tests2);
}

method {:timelimit 40} end(links: seq<nat>)
    requires |links| > 0
    requires permutation(links)
    requires derangement(links)
    requires distinct(links)
{
    assume forall x :: x in links ==> 0 <= x < |links|;
    assume forall x :: x in links ==> multiset(links)[x] == 1;
    assume multiset(links) == multisetRange(|links|);
    var qAct: nat := links[0];
    var i: nat := 0;
    ghost var oldIndex := 0;
    ghost var indices: set<nat> := {0};
    ghost var visited: set<nat> := {};

    while qAct != 0
        invariant 0 <= i <= |links|
        invariant qAct in links
        invariant oldIndex in links
        invariant distinct(links)
        invariant permutation(links)
        invariant derangement(links)
        invariant multiset(links) == multisetRange(|links|)
        invariant multiset(visited + {qAct}) <= multiset(links)
        invariant multiset(indices + {qAct}) <= multiset(links)
        invariant forall x :: x in visited ==> x in indices
        invariant forall x :: x in indices ==> x in links
        invariant forall x :: x in visited ==> exists k :: 0 <= k < |links| && links[k] == x
        invariant forall x :: x in indices ==> exists k :: 0 <= k < |links| && links[k] == x
        invariant oldIndex in visited || oldIndex == 0
        invariant i == |visited|
        invariant visited <= indices
        invariant multiset(visited) <= multiset(links)
        invariant visited + {qAct} <= set x | 0 <= x < |links|
    {
        ghost var oldVisit := visited;
        ghost var oldqAct := qAct;
        ghost var oldOldIndex := oldIndex;
        oldIndex := qAct;
        visited := visited + {qAct};
        indices := indices + {qAct};
        assert forall x :: x in visited ==> exists k :: 0 <= k < |links| && links[k] == x && k in indices;
        qAct := links[qAct];
        i := i + 1;
    }
    assert i == |links|;
    assert multiset(visited) == multisetRange(|links|);
}
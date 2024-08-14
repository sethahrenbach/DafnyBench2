
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
    forall x, y :: x != y && 0 <= x < |s| && 0 <= y < |s| ==> s[x] != s[y]
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
    var qAct: nat := links[0];
    var i: nat := 0;
    ghost var oldIndex := 0;
    ghost var indices: multiset<nat> := multiset{0};
    ghost var visited: multiset<nat> := multiset{};

    while qAct != 0
        invariant 0 <= qAct < |links|
        invariant i <= |links|
        invariant oldIndex < |links|
        invariant multiset(links) == multisetRange(|links|)
        invariant forall x :: x in visited ==> x in links && multiset(links)[x] == 1
        invariant forall x :: x in indices ==> x in links && multiset(links)[x] == 1
        invariant distinct(links)
        invariant derangement(links)
        invariant permutation(links)
        invariant visited <= multisetRange(|links|)
        invariant indices <= multisetRange(|links|)
        invariant forall x :: x in indices ==> x in visited
        invariant forall x :: x in visited ==> exists k :: 0 <= k < |links| && links[k] == x && k in indices
        decreases |links| - i
    {
        ghost var oldVisit := visited;
        ghost var oldqAct := qAct;
        ghost var oldOldIndex := oldIndex;
        oldIndex := qAct;
        visited := visited + multiset{qAct};
        indices := indices + multiset{qAct};

        assert oldqAct == links[oldOldIndex];
        assert forall x :: x in visited ==> exists k :: 0 <= k < |links| && links[k] == x && k in indices;
        assert forall x :: x in oldVisit ==> x in visited;

        qAct := links[qAct];
        i := i + 1;
    }
}

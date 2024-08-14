method Main()
{
    var q := [1,2,4,5,6,7,10,23];
    var i,j := FindAddends(q, 10);
    print "Searching for addends of 10 in q == [1,2,4,5,6,7,10,23]:\n";
    print "Found that q[";
    print i;
    print "] + q[";
    print j;
    print "] == ";
    print q[i];
    print " + ";
    print q[j];
    print " == 10";
}

predicate Sorted(q: seq<int>)
{
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j] 
}

predicate HasAddends(q: seq<int>, x: int)
{
    exists i,j :: 0 <= i < j < |q| && q[i] + q[j] == x
}

method FindAddends(q: seq<int>, x: int) returns (i: nat, j: nat)
    requires Sorted(q) && HasAddends(q, x)
    ensures i < j < |q| && q[i]+q[j] == x
{
    i := 0;
    j := |q| - 1;
    var sum := q[i] + q[j];

    while sum != x
        decreases j - i
        invariant 0 <= i < j < |q|
        invariant exists k, l :: i <= k < l <= j && q[k] + q[l] == x
        invariant sum == q[i] + q[j]
    {
        if (sum > x)
        {
            j := j - 1;
        }
        else // (sum < x)
        {
            i := i + 1;
        }
        sum := q[i] + q[j];
    }
}

predicate IsValidIndex<T>(q: seq<T>, i: nat)
{
    0 <= i < |q|
}

predicate AreOrderedIndices<T>(q: seq<T>, i: nat, j: nat)
{
    0 <= i < j < |q|
}

predicate AreAddendsIndices(q: seq<int>, x: int, i: nat, j: nat)
    requires IsValidIndex(q, i) && IsValidIndex(q, j)
{
    q[i] + q[j] == x
}

predicate HasAddendsInIndicesRange(q: seq<int>, x: int, i: nat, j: nat)
    requires AreOrderedIndices(q, i, j)
{
    HasAddends(q[i..(j + 1)], x)
}

predicate LoopInv(q: seq<int>, x: int, i: nat, j: nat, sum: int)
{
    AreOrderedIndices(q, i, j) &&
    HasAddendsInIndicesRange(q, x, i, j) &&
    sum == q[i] + q[j]
}

lemma LoopInvWhenSumIsBigger(q: seq<int>, x: int, i: nat, j: nat, sum: int)
    requires HasAddends(q, x)
    requires Sorted(q)
    requires sum > x;
    requires LoopInv(q, x, i, j, sum)
    ensures HasAddendsInIndicesRange(q, x, i, j - 1)
{
}
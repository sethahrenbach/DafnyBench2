
//Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
    modifies a
    requires a != null && a.Length > 0 && i < a.Length && j < a.Length
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
{
    a[i], a[j] := a[j], a[i];
}

//b)
//Problem04
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
    var j := lo;
    minIdx := lo;
    while j < a.Length
        invariant lo <= j <= a.Length
        invariant lo <= minIdx < a.Length
        invariant forall x :: lo <= x < j ==> a[minIdx] <= a[x]
    {
        if(a[j] < a[minIdx]) { minIdx := j; }
        j := j + 1;
    }
}

//Problem02
ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}

method selectionSort(a: array<int>)
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures sorted(a[..])
{
    var i := 0;
    while(i < a.Length)
        invariant 0 <= i <= a.Length
        invariant sorted(a[0..i])
    {
        var mx := FindMin(a, i);
        assert forall k :: i <= k < a.Length ==> a[mx] <= a[k];
        assert a[i] <= a[mx];
        assert forall k :: 0 <= k < i ==> a[k] <= a[i];
        swap(a, i, mx);
        i := i + 1;
    }
}

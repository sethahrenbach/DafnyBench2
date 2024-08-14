predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    for i := 0 to a.Length - 1
        invariant 0 <= i <= a.Length
        invariant forall x :: x in res ==> (InArray(a, x) && !InArray(b, x))
        invariant forall k, j :: 0 <= k < j < |res| ==> res[k] != res[j]
    {
        if !InArray(b, a[i]) && a[i] !in res
        {
            res := res + [a[i]];
        }
    }

    ghost var partialSize := |res|;
    for i := 0 to b.Length - 1
        invariant 0 <= i <= b.Length
        invariant forall x :: x in res[0..partialSize] ==> (InArray(a, x) && !InArray(b, x))
        invariant forall x :: x in res[partialSize..|res|] ==> (!InArray(a, x) && InArray(b, x))
        invariant forall k, j :: 0 <= k < j < |res| ==> res[k] != res[j]
    {
        if !InArray(a, b[i]) && b[i] !in res
        {
            res := res + [b[i]];
        }
    }

    result := res;
}

predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are either in a or b, but not in both or neither
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
{
    var res: seq<int> := [];
    for i := 0 to a.Length
        invariant forall k :: k in res ==> !InArray(b, k) && !res.Contains(k)
    {
        if !InArray(b, a[i]) && !res.Contains(a[i])
        {
            res := res + [a[i]];
        }
    }

    ghost var partialSize := res.Count;
    for i := 0 to b.Length
        invariant forall k :: k in res ==> !InArray(a, k) && !res.Contains(k)
    {
        if !InArray(a, b[i]) && !res.Contains(b[i])
        {
            res := res + [b[i]];
        }
    }

    result := res;
}

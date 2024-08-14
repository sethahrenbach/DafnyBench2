predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method Intersection(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    for i := 0 to a.Length - 1
        invariant forall k :: 0 <= k < i ==> (InArray(b, a[k]) && a[k] !in res) ==> a[k] in res
        invariant forall x :: x in res ==> (InArray(a, x) && InArray(b, x))
        invariant forall m, n :: 0 <= m < n < |res| ==> res[m] != res[n]
        invariant |res| <= i
    {
        if InArray(b, a[i]) && a[i] !in res
        {
            res := res + [a[i]];
        }
    }

    result := res;
}
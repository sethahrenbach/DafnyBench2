
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in a and not in b
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: k in res ==> InArray(a, k) && !InArray(b, k)
        invariant forall m, n :: 0 <= m < n < |res| ==> res[m] != res[n]
    {
        if !InArray(b, a[i]) && !InArray(res, a[i])
        {
            res := res + [a[i]];
        }
        i := i + 1;
    }

    result := res;
}

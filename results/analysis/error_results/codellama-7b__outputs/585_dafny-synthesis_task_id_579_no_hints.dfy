
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are either in a or b, but not in both or neither
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    for i := 0 to a.Length
    {
        // Loop invariant: res contains all elements of a that are not in b
        // and all elements of b that are not in a
        invariant forall x :: x in res ==> (InArray(a, x) != InArray(b, x))
        // Loop invariant: res is sorted
        invariant forall i, j :: 0 <= i < j < |res| ==> res[i] < res[j]
        if !InArray(b, a[i]) && a[i] !in res
        {
            // Loop variant: res contains all elements of a that are not in b
            // and all elements of b that are not in a
            variant forall x :: x in res ==> (InArray(a, x) != InArray(b, x))
            res := res + [a[i]];
        }
    }

    ghost var partialSize := |res|;
    for i := 0 to b.Length
    {
        // Loop invariant: res contains all elements of a that are not in b
        // and all elements of b that are not in a
        invariant forall x :: x in res ==> (InArray(a, x) != InArray(b, x))
        // Loop invariant: res is sorted
        invariant forall i, j :: 0 <= i < j < |res| ==> res[i] < res[j]
        if !InArray(a, b[i]) && b[i] !in res
        {
            // Loop variant: res contains all elements of a that are not in b
            // and all elements of b that are not in a
            variant forall x :: x in res ==> (InArray(a, x) != InArray(b, x))
            res := res + [b[i]];
        }
    }

    // Postcondition: the result is sorted
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    result := res;
}

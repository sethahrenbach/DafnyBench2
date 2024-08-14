
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    for i := 0 to a.Length
    {
        // Loop invariant: res contains all the elements that are in both a and b, and are not yet in the output
        // assert InArray(a, a[i]) && InArray(b, a[i]) ==> a[i] !in res;
        if InArray(b, a[i]) && a[i] !in res
        {
            // Loop invariant: res contains all the elements that are in both a and b, and are not yet in the output
            // assert InArray(a, a[i]) && InArray(b, a[i]) ==> a[i] !in res;
            res := res + [a[i]];
        }
    }
    // Loop invariant: res contains all the elements that are in both a and b, and are not yet in the output
    // assert forall x :: x in res ==> InArray(a, x) && InArray(b, x);
    // assert forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j];
    result := res;
}

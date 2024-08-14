
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
    for i := 0 to a.Length
    {
        // Loop invariant: res contains all the elements of a that are not in b
        // and are not already in res
        loop invariant forall x :: x in res ==> InArray(a, x) && !InArray(b, x)
        // Loop invariant: res contains all the elements of a that are not in b
        // and are not already in res
        loop invariant forall x :: x in res ==> InArray(a, x) && !InArray(b, x)
        // Loop variant: i
        loop variant i
        {
            if !InArray(b, a[i]) && a[i] !in res
            {
                // Postcondition: a[i] is in the output
                postcondition InArray(result, a[i])
                // Postcondition: a[i] is not in b
                postcondition !InArray(b, a[i])
                // Postcondition: a[i] is not already in res
                postcondition a[i] !in res
                res := res + [a[i]];
            }
        }
    }

    result := res;
}

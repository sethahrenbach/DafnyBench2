
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    for i := 0 to a.Length
    {
        // Loop Invariant: res contains all unique elements of a[0..i]
        assert forall x :: x in res <==> exists i :: 0 <= i < i && a[i] == x;

        if a[i] !in res
        {
            // Loop Invariant: res contains all unique elements of a[0..i]
            assert forall x :: x in res <==> exists i :: 0 <= i < i && a[i] == x;

            res := res + [a[i]];
        }
    }
    // Postcondition: result contains all unique elements of a
    assert forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x;

    result := res;
}

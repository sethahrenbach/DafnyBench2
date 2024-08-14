
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    var res: seq<int> := [];
    var i := 0;
    while i < a.Length
        invariant forall k :: k in res <==> exists j :: 0 <= j < i && a[j] == k
        invariant 0 <= i <= a.Length
    {
        assert forall k :: k in res <==> exists j :: 0 <= j < i && a[j] == k;
        if i < a.Length && !(a[i] in res)
        {
            res := res + [a[i]];
        }
        i := i + 1;
    }
    result := res;
}

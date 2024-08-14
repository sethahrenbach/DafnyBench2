method buscar(a:array<int>, x:int) returns (r:int)
    requires a != null
    requires a.Length > 0
    ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
    ensures 0 <= r < a.Length ==> a[r] == x
{
    var i := 0;
    r := -1;
    while i < a.Length
        invariant -1 <= r < a.Length
        invariant forall j :: 0 <= j < i ==> a[j] != x
        decreases a.Length - i
    {
        if a[i] == x
        {
            r := i;
            assert 0 <= r < a.Length;
            assert a[r] == x;
            return;
        }
        i := i + 1;
    }
    assert r == -1;
    assert forall j :: 0 <= j < a.Length ==> a[j] != x;
}

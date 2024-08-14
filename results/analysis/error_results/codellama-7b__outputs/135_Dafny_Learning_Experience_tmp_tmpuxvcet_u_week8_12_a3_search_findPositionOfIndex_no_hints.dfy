
method FindPositionOfElement(a: array<int>, Element: int, n1: int, s1: seq<int>) returns (Position: int, Count: int)
    requires n1 == |s1| && 0 <= n1 <= a.Length
    requires forall i:: 0 <= i < |s1| ==> a[i] == s1[i]
    ensures Position == -1 || Position >= 1
    ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
    loop invariant 0 <= Count <= n1
    loop invariant forall i:: 0 <= i < Count ==> a[i] != Element
    loop invariant forall i:: 0 <= i < |s1| ==> a[n1-1-i] == s1[n1-1-i]
    loop invariant forall i:: 0 <= i < |s1| ==> a[n1-1-i] != Element
{
    Count := 0;
    Position := 0;
    while Count != n1
    {
        if a[n1-1-Count] == Element
        {
            Position := Count + 1;
            assert Count >= 1 ==> a[Count -1] != Element;
            assert  a[Count] == Element;

            return Position,Count;
        } 
        Count := Count + 1;
    }
    assert Position != -1 ==> forall i:: 0 <= i < Count ==> a[i] != Element;
    Position := -1;
    assert Position == -1 ==> forall i:: 0 <= i < n1 ==> a[i] != Element;
    assert exists i:: 0 <= i < |s1| && a[i] == Element;
}

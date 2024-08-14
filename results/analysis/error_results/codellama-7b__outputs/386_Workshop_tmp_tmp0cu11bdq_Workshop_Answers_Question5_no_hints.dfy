
method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
{
    var i := 0;
    loopInvariant i >= 0;
    loopInvariant i < a.Length;
    loopInvariant forall j :: 0 <= j < i ==> a[j] == old(a[j]);
    loopInvariant forall j :: i <= j < a.Length ==> a[j] == old(a[(a.Length - 1) - j]);
    while (i < a.Length - 1 - i)
    {
        a[i], a[a.Length - 1 - i] := a[a.Length - 1 - i], a[i];
        i := i + 1;
    }
    assert forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
}

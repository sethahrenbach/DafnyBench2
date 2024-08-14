method rev(a : array<int>)
    requires a != null;
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length - 1) - k]);
{
    var i := 0;
    while (i < a.Length / 2)
        invariant 0 <= i < a.Length / 2
        invariant forall k :: 0 <= k < i ==> a[k] == old(a[a.Length - 1 - k])
        invariant forall k :: a.Length - i <= k < a.Length ==> a[a.Length - 1 - k] == old(a[k])
        invariant forall k :: i <= k < a.Length - i ==> a[k] == old(a[k])
        decreases a.Length / 2 - i
    {
        a[i], a[a.Length - 1 - i] := a[a.Length - 1 - i], a[i];
        i := i + 1;
    }
}
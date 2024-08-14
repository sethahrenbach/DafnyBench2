method RotateRight(a: array<int>)
    requires a.Length > 0
    modifies a
    ensures forall i :: 1 <= i < a.Length ==> a[i] == old(a[i-1])
    ensures a[0] == old(a[a.Length-1])
{
    var temp := a[a.Length - 1];
    var n := a.Length - 1;
    while n > 0
        invariant 0 <= n < a.Length
        invariant forall i :: n < i < a.Length ==> a[i] == old(a[i-1])
        invariant forall i :: n < i < a.Length ==> a[i] == a[i-1]
        invariant forall i :: n < i < a.Length ==> a[i] == old(a[i-1])
        invariant n > 0 ==> a[n] == old(a[n-1])
        decreases n
    {
        a[n] := a[n - 1];
        n := n - 1;
    }
    a[0] := temp;
}
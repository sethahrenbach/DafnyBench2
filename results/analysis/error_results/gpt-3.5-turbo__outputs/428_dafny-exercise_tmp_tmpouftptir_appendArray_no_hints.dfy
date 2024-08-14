method appendArray(a: array<int>, b: array<int>) returns (c: array<int>)
    requires a != null && b != null
    requires a.Length >= 0 && b.Length >= 0
    ensures c.Length == a.Length + b.Length
    ensures forall i :: 0 <= i < a.Length ==> a[i] == c[i]
    ensures forall i :: 0 <= i < b.Length ==> b[i] == c[a.Length + i]
{
    c := new int[a.Length + b.Length];
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] == c[k]
    {
        c[i] := a[i];
        i := i + 1;
    }
    
    while i < b.Length + a.Length
        invariant a.Length <= i <= b.Length + a.Length
        invariant forall k :: a.Length <= k < i ==> b[k - a.Length] == c[k]
    {
        c[i] := b[i - a.Length];
        i := i + 1;
    }
    
    return c;
}
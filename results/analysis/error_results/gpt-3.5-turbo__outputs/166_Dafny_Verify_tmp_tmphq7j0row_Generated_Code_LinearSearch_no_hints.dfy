method LinearSearch<T>(a: array<T>, P: T -> bool) returns (n: int)
    ensures 0 <= n <= a.Length
    ensures n == a.Length || P(a[n])
    ensures forall i :: 0 <= i < n ==> !P(a[i])
{
    var i: int := 0;
    n := a.Length;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> !P(a[k])
        invariant exists k :: 0 <= k < i && P(a[k])
    {
        if P(a[i]) {
            n := i;
            return;
        }
        i := i + 1;
    }
    assert forall j :: 0 <= j < a.Length ==> (j >= i || !P(a[j]));
    assert i == a.Length;
}
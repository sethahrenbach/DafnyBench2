
method join(a:array<int>, b:array<int>) returns (c:array<int>)
    ensures a[..] + b[..] == c[..]
    ensures multiset(a[..] + b[..]) == multiset(c[..])
    ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
    ensures a.Length + b.Length == c.Length
    ensures forall i :: 0 <= i < a.Length ==> c[i] == a[i]
    ensures forall i_2, j_2 ::
        a.Length <= i_2 < c.Length &&
        0 <= j_2 < b.Length && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]
{
    c := new int[a.Length + b.Length];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> c[k] == a[k]
    {
        c[i] := a[i];
        i := i + 1;
    }

    i := a.Length;
    var j := 0;
    while i < c.Length && j < b.Length
        invariant a.Length <= i <= c.Length
        invariant 0 <= j <= b.Length
        invariant forall k :: a.Length <= k < i ==> exists l :: 0 <= l < b.Length && k - l == a.Length && c[k] == b[l]
    {
        c[i] := b[j];
        i := i + 1;
        j := j + 1;
    }
}

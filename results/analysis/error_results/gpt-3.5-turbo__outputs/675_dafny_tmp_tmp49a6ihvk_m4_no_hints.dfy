
datatype Color = Red | White | Blue

predicate Below(c: Color, d: Color)
{
    c == Red || c == d || d == Blue
}

method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var r,w,b := 0, 0, a.Length;
    while w < b
        invariant 0 <= r <= w <= b <= a.Length
        invariant forall k :: 0 <= k < r ==> Below(a[k], Red)
        invariant forall k :: r <= k < w ==> Below(a[k], White)
        invariant forall k :: b <= k < a.Length ==> Below(a[k], Blue)
        invariant forall i, j :: 0 <= i < j < w ==> Below(a[i], a[j])
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        match a[w]
        case Red => 
            assert Below(a[w], Red);
            a[r], a[w] := a[w], a[r];
            r, w := r + 1, w + 1;
        case White => 
            assert Below(a[w], White);
            w := w + 1;
        case Blue => 
            assert Below(a[w], Blue);
            a[b-1], a[w] := a[w], a[b-1];
            b := b - 1;
    }
}

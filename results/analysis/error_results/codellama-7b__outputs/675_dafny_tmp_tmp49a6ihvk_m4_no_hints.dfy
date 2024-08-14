
predicate Below(c1: Color, c2: Color)
{
  c1 == Red && c2 == White
  || c1 == White && c2 == Blue
  || c1 == Blue && c2 == Red
}

method DutchFlag(a: array<Color>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var r, w, b := 0, 0, a.Length;
  while w < b
  {
    match a[w]
    case Red =>
      a[r], a[w] := a[w], a[r];
      r, w := r + 1, w + 1;
    case White =>
      w := w + 1;
    case Blue =>
      a[b-1], a[w] := a[w], a[b-1];
      b := b - 1;
  }
}

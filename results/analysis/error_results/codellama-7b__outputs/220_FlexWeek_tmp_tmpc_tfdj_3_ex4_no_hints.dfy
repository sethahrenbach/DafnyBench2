
method join(a: array<int>, b: array<int>) returns (c: array<int>)
  ensures a[..] + b[..] == c[..]
  ensures multiset(a[..] + b[..]) == multiset(c[..])
  ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
  ensures a.Length + b.Length == c.Length
{
  c := new int[a.Length + b.Length];
  var i := 0;
  while (i < a.Length) {
    c[i] := a[i];
    i := i + 1;
  }

  i := a.Length;
  var j := 0;

  while (i < c.Length && j < b.Length) {
    c[i] := b[j];
    i := i + 1;
    j := j + 1;
  }

  // assert j == b.Length;
  // assert b[..] == b[..b.Length];
  // assert j + a.Length == c.Length;
  // assert multiset(c[..a.Length]) == multiset(a[..a.Length]);
  // assert multiset(b[..]) == multiset(b[..j]);
  // assert multiset(c[a.Length..j+a.Length]) == multiset(c[a.Length..c.Length]);
  // assert multiset(c[a.Length..c.Length]) == multiset(c[a.Length..c.Length]);
  // assert multiset(c[a.Length..c.Length]) == multiset(b[..]);
  // assert multiset(c[0..c.Length]) == multiset(c[0..a.Length]) + multiset(c[a.Length..c.Length]);
}

method join(a: array<int>, b: array<int>) returns (c: array<int>)
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
    while (i < a.Length)
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> c[k] == a[k]
    {
        c[i] := a[i];
        i := i + 1;
    }

    var j := 0;
    while (i < c.Length && j < b.Length)
      invariant a.Length <= i <= c.Length
      invariant 0 <= j <= b.Length
      invariant i == a.Length + j
      invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
      invariant forall k_2, l_2 ::
        a.Length <= k_2 < i &&
        0 <= l_2 < j && k_2 - l_2 == a.Length ==> c[k_2] == b[l_2]
    {
        c[i] := b[j];
        i := i + 1;
        j := j + 1;
    }

    assert j == b.Length;
    assert forall k :: 0 <= k < b.Length ==> b[k] == c[a.Length + k];
    assert j + a.Length == c.Length;
    assert multiset(c[..a.Length]) == multiset(a[..]);
    assert multiset(b[..]) == multiset(b[..j]);
    assert multiset(c[a.Length..a.Length + j]) == multiset(b[..j]);
    assert multiset(c[a.Length..c.Length]) == multiset(b[..]);
    assert multiset(c[..]) == multiset(a[..]) + multiset(b[..]);
}

method Check() {
    var a := new int[3];
    a[0] := 1; a[1] := 2; a[2] := 3;
    var b := new int[2];
    b[0] := 4; b[1] := 5;
    var c := join(a, b);
    assert c.Length == 5;
    assert c[0] == 1;
    assert c[1] == 2;
    assert c[2] == 3;
    assert c[3] == 4;
    assert c[4] == 5;
}
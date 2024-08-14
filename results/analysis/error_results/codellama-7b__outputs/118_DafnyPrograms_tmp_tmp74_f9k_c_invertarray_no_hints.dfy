
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length - 1 - i])
{
  var index := 0;
  loop invariant 0 <= index <= a.Length / 2;
  loop invariant forall i | 0 <= i < index :: a[i] == old(a[i]);
  loop invariant forall i | index <= i < a.Length :: a[i] == old(a[a.Length - 1 - i]);
  loop variant a.Length - index;

  while index < a.Length / 2
    a[index], a[a.Length - 1 - index] := a[a.Length - 1 - index], a[index];
    index := index + 1;
  }
}

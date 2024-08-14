method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..len+dStart] == src[sStart..len+sStart]

{
  if len == 0 { return dest; }
  var i: nat := 0;
  r := new int[dest.Length];
  while (i < r.Length)
    invariant 0 <= i <= r.Length
    invariant r.Length == dest.Length
    invariant forall j :: 0 <= j < i ==> r[j] == dest[j]
  {
    r[i] := dest[i];
    i := i + 1;
  }
  i := 0;
  while (i < len)
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> r[dStart + j] == src[sStart + j]
    invariant forall j :: 0 <= j < dStart ==> r[j] == dest[j]
    invariant forall j :: dStart + len <= j < r.Length ==> r[j] == dest[j]
  {
    r[dStart + i] := src[sStart + i];
    i := i + 1;
  }
  assert forall j :: 0 <= j < dStart ==> r[j] == dest[j];
  assert forall j :: dStart + len <= j < r.Length ==> r[j] == dest[j];
  assert forall j :: 0 <= j < len ==> r[dStart + j] == src[sStart + j];
  return r;
}
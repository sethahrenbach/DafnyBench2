method copy( src: array<int>, sStart: nat, dest: array<int>, dStart: nat, len: nat) returns (r: array<int>)
  requires src.Length >= sStart + len
  requires dest.Length >= dStart + len
  ensures r.Length == dest.Length
  ensures r[..dStart] == dest[..dStart]
  ensures r[dStart + len..] == dest[dStart + len..]
  ensures r[dStart..dStart + len] == src[sStart..sStart + len]
{
  if len == 0 { return dest; }
  var i: nat := 0;
  r := new int[dest.Length];
  
  while (i < r.Length)
    invariant 0 <= i <= r.Length
    invariant forall k :: 0 <= k < i ==> r[k] == dest[k]
  {
    r[i] := dest[i];
    i := i + 1;
  }

  i = 0;
  while (i < len)
    invariant 0 <= i <= len
    invariant forall k :: 0 <= k < i ==> r[dStart + k] == src[sStart + k]
    invariant forall k :: dStart + len <= k < r.Length ==> r[k] == dest[k]
    invariant forall k :: dStart <= k < dStart + len ==> r[k] == src[sStart + k]
  {
    r[dStart + i] := src[sStart + i];
    i := i + 1;
  }
}
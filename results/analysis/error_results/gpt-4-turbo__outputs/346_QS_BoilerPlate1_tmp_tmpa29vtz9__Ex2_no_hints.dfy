
function sorted(s: seq<int>): bool {
  forall k1, k2 :: 0 <= k1 <= k2 < |s| ==> s[k1] <= s[k2]
}

// Ex1

method copyArr(a: array<int>, l: int, r: int) returns (ret: array<int>)
  requires 0 <= l < r <= a.Length
  ensures ret[..] == a[l..r]
{
  var size := r - l;
  ret := new int[size];
  var i := 0;

  while i < size
    invariant 0 <= i <= size
    invariant ret[..i] == a[l..l+i]
  {
    ret[i] := a[i + l];
    i := i + 1;
  }
}

// Ex2

method mergeArr(a: array<int>, l: int, m: int, r: int)
  requires 0 <= l < m < r <= a.Length
  requires sorted(a[l..m]) && sorted(a[m..r])
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a
{
  var left := copyArr(a, l, m);
  var right := copyArr(a, m, r);
  var i := 0;
  var j := 0;
  var cur := l;

  while cur < r
    invariant l <= cur <= r
    invariant 0 <= i <= left.Length
    invariant 0 <= j <= right.Length
    invariant sorted(a[l..cur])
    invariant a[..l] == old(a[..l])
    invariant a[r..] == old(a[r..])
    invariant forall k :: l <= k < cur ==> (k < l + i ? a[k] == left[k - l] : a[k] == right[k - m])
    decreases r - cur
  {
    if (i < left.Length && (j == right.Length || left[i] <= right[j])) {
      a[cur] := left[i];
      i := i + 1;
    } else {
      a[cur] := right[j];
      j := j + 1;
    }
    cur := cur + 1;
  }
}

// Ex3

method sort(a: array<int>)
  ensures sorted(a[..])
  modifies a
{
  if a.Length > 0 {
    sortAux(a, 0, a.Length);
  }
}

method sortAux(a: array<int>, l: int, r: int)
  requires 0 <= l < r <= a.Length
  ensures sorted(a[l..r])
  ensures a[..l] == old(a[..l])
  ensures a[r..] == old(a[r..])
  modifies a
  decreases r - l
{
  if r - l > 1 {
    var m := l + (r - l) / 2;
    sortAux(a, l, m);
    sortAux(a, m, r);
    mergeArr(a, l, m, r);
  }
}

method Max(a:array<nat>) returns (m:int)
  ensures a.Length > 0 ==> forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures a.Length == 0 ==> m == -1
  ensures a.Length > 0 ==> m in a[..]
{
  if (a.Length == 0) {
    return -1;
  }
  var i := 0;
  m := a[0];

  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant a.Length > 0 ==> forall k :: 0 <= k < i ==> m >= a[k]
    invariant a.Length > 0 ==> exists k :: 0 <= k < i && m == a[k]
  {
    assert 0 <= i < a.Length;
    if (a[i] > m) {
      m := a[i];
    }
    i := i + 1;
  }
  return m;
}

method Checker()
{
  var a := new nat[][1, 2, 3, 50, 5, 51];
  var n := Max(a);
  assert a[..] == [1, 2, 3, 50, 5, 51];
  assert n == 51;
}
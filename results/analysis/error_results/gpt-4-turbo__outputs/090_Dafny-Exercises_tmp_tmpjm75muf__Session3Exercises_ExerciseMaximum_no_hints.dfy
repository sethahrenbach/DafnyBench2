
//Algorithm 1: From left to right return the first
method mmaximum1(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
{
  var j := 1;
  i := 0;
  while (j < v.Length)
    invariant 1 <= j <= v.Length
    invariant 0 <= i < j
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    invariant v[i] >= v[0]
  {
    if (v[j] > v[i]) {
      i := j;
    }
    j := j + 1;
  }
}

//Algorithm 2: From right to left return the last
method mmaximum2(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
{
  var j := v.Length - 2;
  i := v.Length - 1;
  while (j >= 0)
    invariant -1 <= j < v.Length
    invariant j < i < v.Length
    invariant forall k :: i <= k < v.Length ==> v[i] >= v[k]
    invariant v[i] >= v[v.Length - 1]
  {
    if (v[j] > v[i]) {
      i := j;
    }
    j := j - 1;
  }
}

method mfirstMaximum(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l :: 0 <= l < i ==> v[i] > v[l]
{
  var j := 1;
  i := 0;
  while (j < v.Length)
    invariant 1 <= j <= v.Length
    invariant 0 <= i < j
    invariant forall k :: 0 <= k < j ==> v[i] >= v[k]
    invariant forall l :: 0 <= l < i ==> v[i] > v[l]
    invariant v[i] >= v[0]
  {
    if (v[j] > v[i]) {
      i := j;
    }
    j := j + 1;
  }
}

method mlastMaximum(v: array<int>) returns (i: int)
  requires v.Length > 0
  ensures 0 <= i < v.Length
  ensures forall k :: 0 <= k < v.Length ==> v[i] >= v[k]
  ensures forall l :: i < l < v.Length ==> v[i] > v[l]
{
  var j := v.Length - 2;
  i := v.Length - 1;
  while (j >= 0)
    invariant -1 <= j < v.Length
    invariant j < i < v.Length
    invariant forall k :: i <= k < v.Length ==> v[i] >= v[k]
    invariant forall l :: i < l < v.Length ==> v[i] > v[l]
    invariant v[i] >= v[v.Length - 1]
  {
    if (v[j] > v[i]) {
      i := j;
    }
    j := j - 1;
  }
}

method mmaxvalue1(v: array<int>) returns (m: int)
  requires v.Length > 0
  ensures m in v[..]
  ensures forall k :: 0 <= k < v.Length ==> m >= v[k]
{
  var i := mmaximum1(v);
  m := v[i];
}

method mmaxvalue2(v: array<int>) returns (m: int)
  requires v.Length > 0
  ensures m in v[..]
  ensures forall k :: 0 <= k < v.Length ==> m >= v[k]
{
  var i := mmaximum2(v);
  m := v[i];
}

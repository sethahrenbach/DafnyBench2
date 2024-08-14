method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{
  var m,n:=0,0;
  d:=if a[0] < b[0] then (b[0]-a[0]) else (a[0]-b[0]);
  assert d==if a[0] < b[0] then (b[0]-a[0]) else (a[0]-b[0]);
  assert forall i,j :: 0<=i<0 && 0<=j<0 ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]);
  assert exists i,j :: i==0 && j==0 && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]);
  while m<a.Length && n<b.Length
    invariant 0<=m<=a.Length && 0<=n<=b.Length
    invariant forall i,j :: 0<=i<m && 0<=j<n ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
    invariant exists i,j :: 0<=i<m && 0<=j<n && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
    decreases a.Length - m + b.Length - n
  {
    ghost var old_m, old_n := m, n;
    var t := if a[m] < b[n] then (b[n]-a[m]) else (a[m]-b[n]);
    assert t>=0;
    if t < d {
      d := t;
      assert exists i,j :: i==m && j==n && 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]);
    } else {
      assert exists i,j :: 0<=i<old_m && 0<=j<old_n && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]);
    }
    if
    case a[m]<=b[n] =>
      m:=m+1;
    case b[n]<=a[m] =>
      n:=n+1;
    assert forall i,j :: 0<=i<old_m && 0<=j<old_n ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]);
  }
  assert forall i,j :: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j]);
}
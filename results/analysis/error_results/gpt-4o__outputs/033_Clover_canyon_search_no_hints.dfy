method CanyonSearch(a: array<int>, b: array<int>) returns (d:nat)
  requires a.Length !=0 && b.Length!=0
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires forall i,j :: 0<=i<j<b.Length ==> b[i]<=b[j]
  ensures exists i,j:: 0<=i<a.Length && 0<=j<b.Length && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
  ensures forall i,j:: 0<=i<a.Length && 0<=j<b.Length ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
{
  var m,n:=0,0;
  d:=if a[0] < b[0] then (b[0]-a[0]) else (a[0]-b[0]);
  while m<a.Length && n<b.Length
    invariant 0 <= m <= a.Length
    invariant 0 <= n <= b.Length
    invariant exists i,j:: 0<=i<=m && 0<=j<=n && d==if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
    invariant forall i,j:: 0<=i<=m && 0<=j<=n ==> d<=if a[i] < b[j] then (b[j]-a[i]) else (a[i]-b[j])
    invariant m < a.Length && n < b.Length ==> d <= if a[m] < b[n] then (b[n]-a[m]) else (a[m]-b[n])
  {
    assert 0 <= m < a.Length;
    assert 0 <= n < b.Length;
    var t := if a[m] < b[n] then (b[n]-a[m]) else (a[m]-b[n]);
    d:=if t<d then t else d;
    if m < a.Length && n < b.Length {
      if a[m] <= b[n] {
        m := m + 1;
      } else {
        n := n + 1;
      }
    }
  }
}
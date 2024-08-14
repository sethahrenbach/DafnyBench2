
method selSort (a:array<int>, c:int, f:int)
modifies a
requires 0 <= c <= f <= a.Length
ensures sorted_seg(a,c,f)
ensures multiset(a[c..f]) == old(multiset(a[c..f]))
ensures a[..c]==old(a[..c]) && a[f..]==old(a[f..])
{
  if (c<=f-1) {
    var i:=c;
    while (i<f-1) {
      var less:=i;
      var j:=i+1;
      while (j<f) {
        if (a[j]<a[less]) {less:=j;}
        j:=j+1;
      }
      a[i],a[less]:=a[less],a[i];
      i:=i+1;
    }
  }
}

predicate sorted_seg(a:array<int>, i:int, j:int)
requires 0 <= i <= j <= a.Length
ensures sorted(a[i..j])
{
  if i < j {
    sorted_seg(a, i, j-1);
    a[j] <= a[j-1];
  }
}

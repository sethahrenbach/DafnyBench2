method onlineMax(a: array<int>, x: int) returns (ghost m:int, p:int)
  requires 1<=x<a.Length
  requires a.Length!=0
  ensures x<=p<a.Length
  ensures forall i::0<=i<x==> a[i]<=m
  ensures exists i::0<=i<x && a[i]==m
  ensures x<=p<a.Length-1 ==> (forall i::0<=i<p ==> a[i]<a[p])
  ensures (forall i::x<=i<a.Length && a[i]<=m) ==> p==a.Length-1
{
  p:= 0;
  var best := a[0];
  var i:=1;
  // Loop invariant for the first loop
  invariant 1<=i<=x
  invariant forall j::0<=j<i ==> a[j]<=best
  invariant exists j::0<=j<i && a[j]==best
  while i<x
  {
    if a[i]>best {
      best:=a[i];
    }
    i:=i+1;
  }
  m:=best;
  i:=x;
  // Loop invariant for the second loop
  invariant x<=i<=a.Length
  invariant forall j::x<=j<i ==> a[j]<=best
  invariant p==0 || (x<=p<i && a[p]>best)
  while i<a.Length
  {
    if a[i]>best {
      p:=i;
      best:=a[i]; // Update best to maintain the invariant
    }
    i:=i+1;
  }
  if p==0 {
    p:=a.Length-1;
  }
}
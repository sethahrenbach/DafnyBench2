
method mCountMin(v:array<int>) returns (c:int)
reads v
requires v.Length>0
ensures c==countMin(v,min(v,v.Length),v.Length)
{
  var i:=1;
  c:=1;
  var mini:=v[0];
  while(i<v.Length)
  {
    // Loop invariant: c is the number of elements in v[0..i] that are less than or equal to the minimum element of v[0..i]
    loop invariant 0<=i<=v.Length && c==countMin(v,min(v,i),i)
    // Postcondition: c is the number of elements in v[0..i] that are less than or equal to the minimum element of v[0..i]
    postcondition c==countMin(v,min(v,i),i)
    if(v[i]==mini){
      c:=c + 1;
    }
    else if(v[i]<mini){
      c:=1;
      mini:=v[i];
    }
    i:=i+1;
  }
}

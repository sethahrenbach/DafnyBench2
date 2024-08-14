
method mfirstCero(v:array<int>) returns (i:int)
  ensures 0 <=i<=v.Length
  ensures forall j:: 0<=j<i ==> v[j]!=0 
  ensures i!=v.Length ==> v[i]==0  
{
  i:=0;
  while (i<v.Length)
  {
    if (v[i]==0) break;
    i:=i+1;
  }
  assert i!=v.Length ==> v[i]==0;
  assert forall j:: 0<=j<i ==> v[j]!=0;
  return i;
}

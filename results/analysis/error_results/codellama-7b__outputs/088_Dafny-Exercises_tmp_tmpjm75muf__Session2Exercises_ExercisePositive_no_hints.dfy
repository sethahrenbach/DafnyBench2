
method mpositive(v:array<int>) returns (b:bool)
  ensures b==(forall i:int :: i<v.Length ==> v[i]>=0)
{
  var i:=0;
  while i<v.Length
  {
    if v[i]<0
    {
      return false;
    }
    i:=i+1;
  }
  return true;
}

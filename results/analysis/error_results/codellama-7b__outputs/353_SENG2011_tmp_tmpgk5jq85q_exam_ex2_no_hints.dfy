
method Getmini(a:array<int>) returns(mini:nat)
  requires a.Length > 0
  ensures 0 <= mini < a.Length
  ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x]
  ensures forall x :: 0 <= x < mini ==> a[mini] < a[x]
{
  // find mini
  var min:int := a[0];
  var i:int := 0;
  while i < a.Length
  {
    if a[i] < min
    {
      min := a[i];
    }
    i := i + 1;
  }

  //assert min in a[..]; // min is in a -> it will be found by this loop
  // find first occurance
  var k:int := 0;
  while k < a.Length
  {
    if a[k] == min
    {
      return k;
    }
    k := k + 1;
  }
}

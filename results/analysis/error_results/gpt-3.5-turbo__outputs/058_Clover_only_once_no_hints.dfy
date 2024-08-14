method only_once<T>(a: array<T>, key: T) returns (b: bool)
  requires a != null
  ensures (multiset(a[..])[key] == 1) <==> b
{
  var i := 0;
  b := false;
  var keyCount := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant keyCount <= 1
    invariant (multiset(a[..])[key] == keyCount) || (multiset(a[..])[key] == keyCount + 1)
  {
    if a[i] == key
    {
      keyCount := keyCount + 1;
    }
    if keyCount == 1
    { 
      b := true; 
      assert (multiset(a[..])[key] == keyCount);
    }
    else
    { 
      b := false; 
      assert (multiset(a[..])[key] == keyCount);
    }
    i := i + 1;
  }
}


method UniqueProduct (arr: array<int>) returns (product: int)
  ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
  var p := 1;
  var seen: set<int> := {};

  for i := 0 to arr.Length
  {
    if ! (arr[i] in seen) {
      seen := seen + { arr[i] };
      p := p * arr[i];
      // Loop Invariant: The product of the elements in the set "seen" is equal to the product of the elements in the original array
      // that have not yet been added to the set.
      loop invariant p == SetProduct((set i | 0 <= i < arr.Length :: arr[i]) - seen);
      // Assertion: The element being added to the set is not already in the set.
      assert arr[i] not in seen;
      // Lemma: The product of the elements in the set "seen" is equal to the product of the elements in the original array
      // that have not yet been added to the set.
      lemma SetProductLemma(s: set <int>, x: int) 
      requires x in s
      ensures SetProduct(s - {x}) * x == SetProduct(s)
      {
        if s != {}
        {
          var y :| y in s && y * SetProduct(s - {y}) == SetProduct(s);
          if y == x {}
          else {
            calc {
              SetProduct(s);
              y * SetProduct(s - {y});
              { SetProductLemma(s - {y}, x); }
              y * x * SetProduct(s - {y} - {x});
              y * x * SetProduct(s - {x} - {y});
              x * y * SetProduct(s - {x} - {y});
              { SetProductLemma(s - {x}, y); }
              x * SetProduct(s - {x});
            }
          }
        }
      }
    }
  }
  product := p;
}

ghost function SetProduct(s : set<int>) : int
{
  if s == {} then 1
  else var x :| x in s; 
       x * SetProduct(s - {x})
}


method FirstEvenOddIndices(lst: seq<int>) returns (evenIndex: int, oddIndex: int)
  requires |lst| >= 2
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures 0 <= evenIndex < |lst|
  ensures 0 <= oddIndex < |lst|
  ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
  ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
  for i := 0 to |lst| do
    if IsEven(lst[i]) then
      evenIndex := i;
      break;
    if IsOdd(lst[i]) then
      oddIndex := i;
      break;
  }
}

method ProductEvenOdd(lst: seq<int>) returns (product: int)
  requires |lst| >= 2
  requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
  requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
  ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                         0 <= j < |lst| && IsOdd(lst[j])  && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
{
  var evenIndex, oddIndex := FirstEvenOddIndices(lst);
  // Loop Invariant: evenIndex and oddIndex are the indices of the first even and odd elements in lst, respectively.
  // This invariant is necessary to ensure that the product is calculated correctly.
  assert evenIndex >= 0 && evenIndex < |lst| && IsEven(lst[evenIndex]);
  assert oddIndex >= 0 && oddIndex < |lst| && IsOdd(lst[oddIndex]);
  product := lst[evenIndex] * lst[oddIndex];
}

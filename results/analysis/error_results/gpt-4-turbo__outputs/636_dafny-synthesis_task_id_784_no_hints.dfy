predicate IsEven(n: int)
{
    n % 2 == 0
}

predicate IsOdd(n: int)
{
    n % 2 != 0
}

predicate IsFirstEven(evenIndex: int, lst: seq<int>)
    requires 0 <= evenIndex < |lst|
    requires IsEven(lst[evenIndex])
{
    forall i :: 0 <= i < evenIndex ==> IsOdd(lst[i])
}

predicate IsFirstOdd(oddIndex: int, lst: seq<int>)
    requires 0 <= oddIndex < |lst|
    requires IsOdd(lst[oddIndex])
{
    forall i :: 0 <= i < oddIndex ==> IsEven(lst[i])
}

method FirstEvenOddIndices(lst : seq<int>) returns (evenIndex: int, oddIndex : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= evenIndex < |lst|
    ensures 0 <= oddIndex < |lst|
    ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
    evenIndex := -1;
    oddIndex := -1;

    var i := 0;
    while (i < |lst|)
        invariant 0 <= i <= |lst|
        invariant evenIndex == -1 || (0 <= evenIndex < i && IsEven(lst[evenIndex]) && forall j :: 0 <= j < evenIndex ==> IsOdd(lst[j]))
        invariant oddIndex == -1 || (0 <= oddIndex < i && IsOdd(lst[oddIndex]) && forall j :: 0 <= j < oddIndex ==> IsEven(lst[j]))
    {
        if (evenIndex == -1 && IsEven(lst[i]))
        {
            evenIndex := i;
        }
        if (oddIndex == -1 && IsOdd(lst[i]))
        {
            oddIndex := i;
        }
        i := i + 1;
    }
    assert evenIndex != -1 && oddIndex != -1; // Ensure indices are found
    assert IsFirstEven(evenIndex, lst); // Validate postconditions
    assert IsFirstOdd(oddIndex, lst); // Validate postconditions
}

method ProductEvenOdd(lst: seq<int>) returns (product : int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) && 
                           0 <= j < |lst| && IsOdd(lst[j])  && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}
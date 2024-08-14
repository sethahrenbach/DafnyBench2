
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

method FirstEvenOddIndices(lst: seq<int>) returns (evenIndex: int, oddIndex: int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures 0 <= evenIndex < |lst|
    ensures 0 <= oddIndex < |lst|
    ensures IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst)
    ensures IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst)
{
    var i := 0;
    evenIndex := -1;
    oddIndex := -1;
    while i < |lst
        invariant 0 <= i <= |lst
        invariant (evenIndex == -1 || IsEven(lst[evenIndex])) && (oddIndex == -1 || IsOdd(lst[oddIndex]))
        invariant forall k :: 0 <= k < i ==> IsOdd(lst[k]) || IsEven(lst[k])
        invariant exists k :: 0 <= k < i && IsEven(lst[k]) ==> evenIndex != -1
        invariant exists k :: 0 <= k < i && IsOdd(lst[k]) ==> oddIndex != -1
    {
        if IsEven(lst[i])
        {
            evenIndex := i;
            break;
        }
        i := i + 1;
    }

    i := 0;
    while i < |lst
        invariant 0 <= i <= |lst
        invariant (evenIndex == -1 || IsEven(lst[evenIndex])) && (oddIndex == -1 || IsOdd(lst[oddIndex]))
        invariant forall k :: 0 <= k < i ==> IsOdd(lst[k]) || IsEven(lst[k])
        invariant exists k :: 0 <= k < i && IsOdd(lst[k]) ==> oddIndex != -1
        invariant exists k :: 0 <= k < i && IsEven(lst[k]) ==> evenIndex != -1
    {
        if IsOdd(lst[i])
        {
            oddIndex := i;
            break;
        }
        i := i + 1;
    }
}

method ProductEvenOdd(lst: seq<int>) returns (product: int)
    requires |lst| >= 2
    requires exists i :: 0 <= i < |lst| && IsEven(lst[i])
    requires exists i :: 0 <= i < |lst| && IsOdd(lst[i])
    ensures exists i, j :: 0 <= i < |lst| && IsEven(lst[i]) && IsFirstEven(i, lst) &&
                           0 <= j < |lst| && IsOdd(lst[j]) && IsFirstOdd(j, lst) && product == lst[i] * lst[j]
{
    var evenIndex, oddIndex := FirstEvenOddIndices(lst);
    product := lst[evenIndex] * lst[oddIndex];
}

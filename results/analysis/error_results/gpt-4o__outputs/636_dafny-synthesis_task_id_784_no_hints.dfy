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
    var foundEven := false;
    var foundOdd := false;
    evenIndex := -1;
    oddIndex := -1;

    for i := 0 to |lst|
        invariant 0 <= i <= |lst|
        invariant !foundEven ==> evenIndex == -1
        invariant foundEven ==> 0 <= evenIndex < i && IsEven(lst[evenIndex])
        invariant foundEven ==> forall j :: 0 <= j < evenIndex ==> IsOdd(lst[j])
        invariant !foundOdd ==> oddIndex == -1
        invariant foundOdd ==> 0 <= oddIndex < i && IsOdd(lst[oddIndex])
        invariant foundOdd ==> forall j :: 0 <= j < oddIndex ==> IsEven(lst[j])
        invariant foundEven ==> evenIndex < i
        invariant foundOdd ==> oddIndex < i
        invariant !(foundEven && foundOdd) ==> evenIndex == -1 || oddIndex == -1
    {
        if !foundEven && IsEven(lst[i])
        {
            evenIndex := i;
            foundEven := true;
        }
        if !foundOdd && IsOdd(lst[i])
        {
            oddIndex := i;
            foundOdd := true;
        }
        if foundEven && foundOdd {
            break;
        }
    }
    assert 0 <= evenIndex < |lst|;
    assert 0 <= oddIndex < |lst|;
    assert IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst);
    assert IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst);
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
    assert IsEven(lst[evenIndex]) && IsFirstEven(evenIndex, lst);
    assert IsOdd(lst[oddIndex]) && IsFirstOdd(oddIndex, lst);
    assert product == lst[evenIndex] * lst[oddIndex];
}
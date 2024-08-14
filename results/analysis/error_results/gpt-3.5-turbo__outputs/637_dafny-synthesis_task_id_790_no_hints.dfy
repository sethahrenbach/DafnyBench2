predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsEvenAtIndexEven(lst: seq<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]))
{
    result := true;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant forall j :: 0 <= j < i ==> (IsEven(j) ==> IsEven(lst[j]))
    {
        assert IsEven(i) ==> IsEven(lst[i]);
        if IsEven(i) && !IsEven(lst[i])
        {
            result := false;
            break;
        }
        i := i + 1;
    }
    assert result <==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]));
    assert result ==> forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]));
    assert forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i])) ==> result;
    assert forall i :: 0 <= i < |lst| ==> (IsEven(i) ==> IsEven(lst[i]));
}
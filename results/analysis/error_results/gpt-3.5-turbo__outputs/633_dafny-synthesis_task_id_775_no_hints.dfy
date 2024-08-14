predicate IsOdd(n: int)
{
    n % 2 == 1
}

method IsOddAtIndexOdd(a: array<int>) returns (result: bool)
    ensures result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]))
{
    result := true;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant result <==> forall j :: 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a[j]))
    {
        assert IsOdd(i) ==> IsOdd(a[i]);
        if IsOdd(i) && !IsOdd(a[i])
        {
            result := false;
            break;
        }
        i := i + 1;
    }
    assert result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]));
    assert forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]));
    assert result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]));
    assert forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]));
    assert result <==> forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]));
    assert forall i :: 0 <= i < a.Length ==> (IsOdd(i) ==> IsOdd(a[i]));
    assert i == a.Length;
}
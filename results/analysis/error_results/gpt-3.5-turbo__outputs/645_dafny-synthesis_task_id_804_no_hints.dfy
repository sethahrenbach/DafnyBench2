
predicate IsEven(n: int)
{
    n % 2 == 0
}

method IsProductEven(a: array<int>) returns (result: bool)
    ensures result <==> exists i :: 0 <= i < a.Length && IsEven(a[i])
{
    result := false;
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> !IsEven(a[j]) ==> !result
        invariant exists j :: 0 <= j < i && IsEven(a[j]) <==> result
    {
        if IsEven(a[i])
        {
            result := true;
            break;
        }
        i := i + 1;
    }
    assert result ==> exists j :: 0 <= j < a.Length && IsEven(a[j]);
    assert !result ==> forall j :: 0 <= j < a.Length ==> !IsEven(a[j]);
}


method IsGreater(n: int, a: array<int?>) returns (result: bool)
    requires a != null
    ensures result ==> forall i :: 0 <= i < a.Length ==> n > a[i]!
    ensures !result ==> exists i :: 0 <= i < a.Length && n <= a[i]!
{
    result := true;
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant result ==> forall j :: 0 <= j < i ==> n > a[j]!
      invariant !result ==> exists j :: 0 <= j < i && n <= a[j]!
    {
        if a[i] != null && n <= a[i]!
        {
            result := false;
            assert exists j :: 0 <= j < i && n <= a[j]!;
            break;
        }
        i := i + 1;
    }
    assert result ==> forall k :: 0 <= k < a.Length ==> n > a[k]!;
    assert !result ==> exists k :: 0 <= k < a.Length && n <= a[k]!;
}

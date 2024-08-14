
method Evens(a: array<int>) returns (c: array<int>)
    requires a.Length >= 0
    modifies c
    ensures c.Length == a.Length
    ensures forall i, j: 0 <= i < a.Length && 0 <= j < a.Length ==> c[i, j] == a[i, j]
{
    c := new array<int>(a.Length, a.Length);
    var m := 0;
    while m < a.Length
        modifies c
    {
        var n := 0;
        while n < a.Length
            modifies c
        {
            if a[m, n] % 2 == 0
                c[m, n] := a[m, n];
            else
                c[m, n] := a[m, n] + 1;
            n := n + 1;
        }
        m := m + 1;
    }
}

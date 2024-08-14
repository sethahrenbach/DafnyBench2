function sum(a: array<int>, i: int) returns (result: int)
    requires 0 <= i < a.Length
    reads a
{
    if i == 0 {
        result := a[i];
    } else {
        result := a[i] + sum(a, i - 1);
    }
}

method cumsum(a: array<int>, b: array<int>)
    requires a.Length == b.Length && a.Length > 0 && a != b
    ensures forall i :: 0 <= i < a.Length ==> b[i] == sum(a, i)
    modifies b
{
    b[0] := a[0]; // Initialise le premier élément de b
    var i := 1;
    
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> b[j] == sum(a, j)
    {
        b[i] := b[i - 1] + a[i]; // Calcule la somme cumulée pour chaque élément
        i := i + 1;
    }
}
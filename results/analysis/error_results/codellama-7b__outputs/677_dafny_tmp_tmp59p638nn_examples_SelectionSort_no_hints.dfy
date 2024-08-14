
method SelectionSort(a: array<int>)
    modifies a
    ensures Sorted(a)
{
    for i := 0 to a.Length
    {
        ghost var minValue := a[i];
        for j := i + 1 to a.Length
        {
            label L:
            if a[j] < minValue {
                minValue := a[j];
            }
            if a[j] < a[i] {
                a[i], a[j] := a[j], a[i];
            }
        }
    }
}

function Sorted(a: array<int>): bool
    ensures a == sorted(a)
{
    for i := 0 to a.Length - 1
    {
        if a[i] > a[i+1] {
            return false;
        }
    }
    return true;
}

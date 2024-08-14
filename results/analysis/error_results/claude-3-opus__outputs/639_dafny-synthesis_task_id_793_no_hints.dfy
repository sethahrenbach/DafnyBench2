method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos == arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    pos := -1;
    for i := 0 to arr.Length
        invariant 0 <= i <= arr.Length
        invariant pos == -1 || (0 <= pos < i && arr[pos] == elem)
        invariant forall k :: 0 <= k < i ==> arr[k] <= elem
    {
        if i < arr.Length && arr[i] == elem
        {
            pos := i;
        }
    }
    if pos != -1
    {
        assert arr[pos] == elem;
        if pos < arr.Length - 1
        {
            assert arr[pos + 1] > elem;
        }
    }
}
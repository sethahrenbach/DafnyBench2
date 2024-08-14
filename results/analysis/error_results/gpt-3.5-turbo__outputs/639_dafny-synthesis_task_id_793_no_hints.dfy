
method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos <= arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    pos := -1;
    var i := 0;
    while i < arr.Length
        invariant -1 <= pos < arr.Length;
        invariant forall k :: 0 <= k < i ==> (arr[k] != elem || pos == k);
        decreases arr.Length - i;
    {
        if arr[i] == elem
        {
            pos := i;
        }
        i := i + 1;
    }
    pos
}

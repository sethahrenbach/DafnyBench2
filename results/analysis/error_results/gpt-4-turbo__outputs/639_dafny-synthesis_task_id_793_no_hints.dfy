method LastPosition(arr: array<int>, elem: int) returns (pos: int)
    requires arr.Length > 0
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem && (pos == arr.Length - 1 || arr[pos + 1] > elem))
    ensures forall i :: 0 <= i < arr.Length ==> arr[i] == old(arr[i])
{
    pos := -1;
    for i := 0 to arr.Length - 1
        invariant -1 <= pos <= i
        invariant forall k :: 0 <= k < i ==> (arr[k] == elem ==> pos >= k)
        invariant pos == -1 || (0 <= pos < arr.Length && arr[pos] == elem)
        invariant forall k :: 0 <= k < i ==> (arr[k] != elem || k <= pos)
        invariant forall k :: 0 <= k <= i ==> (arr[k] == elem ==> arr[pos] == elem)
    {
        if arr[i] == elem
        {
            pos := i;
        }
    }
}
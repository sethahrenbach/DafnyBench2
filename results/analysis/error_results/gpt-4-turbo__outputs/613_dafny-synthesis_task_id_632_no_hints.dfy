method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    ensures arr.Length == old(arr.Length)
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    ensures forall n, m :: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l :: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
{
    var i := 0;
    var j := 0;

    while j < arr.Length
        invariant 0 <= i <= j <= arr.Length
        invariant forall k :: 0 <= k < i ==> arr[k] != 0
        invariant forall k :: i <= k < j ==> arr[k] == 0
        invariant multiset(arr[..j]) == multiset(old(arr[..j]))
        invariant forall n, m :: 0 <= n < m < j && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
                  exists k, l :: 0 <= k < l < j && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
        invariant forall k :: j <= k < arr.Length ==> arr[k] == old(arr[k])
        invariant forall k :: i <= k < arr.Length && arr[k] == 0 ==> forall l :: k < l < arr.Length ==> arr[l] == 0
    {
        if arr[j] != 0
        {
            if i != j
            {
                swap(arr, i, j);
            }
            i := i + 1;
        }
        j := j + 1;
    }
}

method swap(arr: array<int>, i: int, j: int)
    requires arr.Length > 0
    requires 0 <= i < arr.Length && 0 <= j < arr.Length
    modifies arr
    ensures arr[i] == old(arr[j]) && arr[j] == old(arr[i])
    ensures forall k :: 0 <= k < arr.Length && k != i && k != j ==> arr[k] == old(arr[k])
    ensures multiset(arr[..]) == multiset(old(arr[..]))
{
    var tmp := arr[i];
    arr[i] := arr[j];
    arr[j] := tmp;
}
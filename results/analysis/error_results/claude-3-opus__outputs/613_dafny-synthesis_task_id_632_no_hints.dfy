method MoveZeroesToEnd(arr: array<int>)
    requires arr.Length >= 2
    modifies arr
    // Same size
    ensures arr.Length == old(arr.Length)
    // Zeros to the right of the first zero
    ensures forall i, j :: 0 <= i < j < arr.Length && arr[i] == 0 ==> arr[j] == 0
    // The final array is a permutation of the original one
    ensures multiset(arr[..]) == multiset(old(arr[..]))
    // Relative order of non-zero elements is preserved
    ensures forall n, m /* on old array */:: 0 <= n < m < arr.Length && old(arr[n]) != 0 && old(arr[m]) != 0 ==> 
            exists k, l /* on new array */:: 0 <= k < l < arr.Length && arr[k] == old(arr[n]) && arr[l] == old(arr[m])
    // Number of zeros is preserved
    ensures count(arr[..], 0) == count(old(arr[..]), 0)
{
    var i := 0;
    var j := 0;
    ghost var oldarr := arr[..];

    while j < arr.Length
        invariant 0 <= i <= j <= arr.Length
        invariant forall k :: 0 <= k < i ==> arr[k] != 0
        invariant forall k :: i <= k < j ==> arr[k] == 0
        invariant forall k :: j <= k < arr.Length ==> arr[k] == oldarr[k]
        invariant multiset(arr[..]) == multiset(oldarr)
        invariant forall n, m :: 0 <= n < m < j && oldarr[n] != 0 && oldarr[m] != 0 ==>
                  exists k, l :: 0 <= k < l < i && arr[k] == oldarr[n] && arr[l] == oldarr[m]
        invariant count(arr[..], 0) == count(oldarr, 0)
    {
        ghost var prevArr := arr[..];
        ghost var prevI := i;

        if arr[j] != 0
        {
            swap(arr, i, j);
            i := i + 1;
        }
        j := j + 1;

        if arr[j-1] != 0 {
            assert forall n, m :: 0 <= n < m < j-1 && oldarr[n] != 0 && oldarr[m] != 0 ==>
                  exists k, l :: 0 <= k < l < prevI && prevArr[k] == oldarr[n] && prevArr[l] == oldarr[m];
            assert prevArr[prevI] == oldarr[j-1];
        }
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

function count(arr: seq<int>, value: int) : (c: nat)
    ensures c <= |arr|
{
    if |arr| == 0 then 0 else (if arr[0] == value then 1 else 0) + count(arr[1..], value)
}
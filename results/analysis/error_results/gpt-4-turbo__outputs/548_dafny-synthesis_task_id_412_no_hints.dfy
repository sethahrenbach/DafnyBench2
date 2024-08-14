
/**
 * Remove odd numbers from an array of numbers
 **/

predicate IsEven(n: int)
{
    n % 2 == 0
}

method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
    // All numbers in the output are even and exist in the input 
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // All even numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
{
    evenList := [];
    for i := 0 to arr.Length - 1
        invariant 0 <= i < arr.Length
        invariant forall k :: 0 <= k < |evenList| ==> IsEven(evenList[k])
        invariant forall k :: 0 <= k < |evenList| ==> evenList[k] in arr[..]
        invariant forall k :: 0 <= k < i && IsEven(arr[k]) ==> arr[k] in evenList
        invariant forall k :: 0 <= k < i ==> (IsEven(arr[k]) ==> arr[k] in evenList)
        invariant forall k :: 0 <= k < |evenList| ==> exists j :: 0 <= j < i && arr[j] == evenList[k]
    {
        if IsEven(arr[i])
        {
            evenList := evenList + [arr[i]];
        }
    }
}

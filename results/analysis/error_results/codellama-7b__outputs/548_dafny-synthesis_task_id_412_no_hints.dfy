
method RemoveOddNumbers(arr: array<int>) returns (evenList: seq<int>)
    // All numbers in the output are even and exist in the input 
    ensures forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // All even numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList
{
    // Loop invariant: evenList contains only even numbers that exist in arr
    loop invariant forall i :: 0 <= i < |evenList| ==> IsEven(evenList[i]) && evenList[i] in arr[..]
    // Loop invariant: evenList contains only even numbers that exist in arr
    loop invariant forall i :: 0 <= i < arr.Length && IsEven(arr[i]) ==> arr[i] in evenList

    evenList := [];
    for i := 0 to arr.Length
    {
        // Assert that the current element is even
        assert IsEven(arr[i]);

        // Assert that the current element is in the input array
        assert arr[i] in arr[..];

        // Add the current element to the output list if it is even
        if IsEven(arr[i])
        {
            evenList := evenList + [arr[i]];
        }
    }
}

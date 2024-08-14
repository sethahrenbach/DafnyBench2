
method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
    // Loop invariant: all numbers in the output are odd and exist in the input
    loop invariant forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // Loop invariant: all odd numbers in the input are in the output
    loop invariant forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList

    oddList := [];
    for i := 0 to arr.Length
    {
        // Assert that the current number is odd
        assert IsOdd(arr[i]);

        // Assert that the current number is in the input
        assert arr[i] in arr[..];

        if IsOdd(arr[i])
        {
            // Assert that the current number is in the output
            assert arr[i] in oddList;

            oddList := oddList + [arr[i]];
        }
    }
}

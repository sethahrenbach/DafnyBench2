/**
 * Filter odd numbers from an array of numbers
 **/

predicate IsOdd(n: int)
{
    n % 2 != 0
}

method FilterOddNumbers(arr: array<int>) returns (oddList: seq<int>)
    // All numbers in the output are odd and exist in the input 
    ensures forall i :: 0 <= i < |oddList| ==> IsOdd(oddList[i]) && oddList[i] in arr[..]
    // All odd numbers in the input are in the output
    ensures forall i :: 0 <= i < arr.Length && IsOdd(arr[i]) ==> arr[i] in oddList
{
    oddList := [];
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant oddList == [arr[j] | j in 0..i | IsOdd(arr[j])]
        invariant forall k :: 0 <= k < i ==> IsOdd(oddList[k]) && oddList[k] in arr[..]
    {
        if IsOdd(arr[i])
        {
            oddList := oddList + [arr[i]];
        }
        i := i + 1;
    }
}

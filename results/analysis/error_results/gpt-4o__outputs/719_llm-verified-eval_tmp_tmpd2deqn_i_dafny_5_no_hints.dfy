method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
{
    interspersed := [];
    var j := 0;
    while j < |numbers|
        invariant 0 <= j <= |numbers|
        invariant |interspersed| == if j > 0 then 2 * j - 1 else 0
        invariant forall k :: 0 <= k < |interspersed| ==> k % 2 == 0 ==> interspersed[k] == numbers[k / 2]
        invariant forall k :: 0 <= k < |interspersed| ==> k % 2 == 1 ==> interspersed[k] == delimiter
    {
        if j > 0 {
            interspersed := interspersed + [delimiter];
        }
        interspersed := interspersed + [numbers[j]];
        j := j + 1;
    }
}
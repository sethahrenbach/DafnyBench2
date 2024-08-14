
method intersperse(numbers: seq<int>, delimiter: int) returns (interspersed: seq<int>)
    ensures |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2]
    ensures forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter
{
    interspersed := [];
    var i: int := 0;
    while i < |numbers|
        invariant 0 <= i <= |numbers|
        invariant |interspersed| == if i > 0 then 2 * i - 1 else 0
        invariant forall j :: 0 <= j < i ==> interspersed[2*j] == numbers[j]
        invariant forall j :: 0 <= j < i ==> interspersed[2*j+1] == delimiter
    {
        if i > 0 {
            interspersed := interspersed + [delimiter];
        }
        interspersed := interspersed + [numbers[i]];
        i := i + 1;
    }
    assert |interspersed| == if |numbers| > 0 then 2 * |numbers| - 1 else 0;
    assert forall i :: 0 <= i < |interspersed| ==> i % 2 == 0 ==> 
                interspersed[i] == numbers[i / 2];
    assert forall i :: 0 <= i < |interspersed| ==> i % 2 == 1 ==>
                interspersed[i] == delimiter;
}

function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m
}

method max(numbers: seq<int>) returns (result: int)
requires numbers != []
ensures isMax(result, numbers)
{
    result := numbers[0];
    var i: nat := 1;
    while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant isMax(result, numbers[0..i])
    {
        if numbers[i] > result {
            result := numbers[i];
        }
        i := i + 1;
    }
}

method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 <= i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
    var m := numbers[0];
    result := [m];
    var i: nat := 1;
    while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> isMax(result[j], numbers[0..j+1])
    {
        if i < |numbers| && numbers[i] > m {
            m := numbers[i];
        }
        result := result + [m];
        i := i + 1;
    }
}
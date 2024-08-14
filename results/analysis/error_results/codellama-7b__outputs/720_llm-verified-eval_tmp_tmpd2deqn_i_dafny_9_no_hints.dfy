
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
  requires numbers != []
  ensures |result| == |numbers|
  ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
{
  var m := numbers[0];
  result := [m];
  for i := 1 to |numbers| {
    // Loop invariant: m is the maximum of the first i elements of numbers
    assert m in numbers && forall j :: 0 <= j < i ==> numbers[j] <= m;

    if numbers[i] > m {
      m := numbers[i];
    }
    result := result + [m];
  }
}

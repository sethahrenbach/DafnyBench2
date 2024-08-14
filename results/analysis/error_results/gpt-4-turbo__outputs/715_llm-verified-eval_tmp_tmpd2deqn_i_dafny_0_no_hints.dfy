function absolute(x: real): real
{
  if x < 0.0 then -x else x
}

method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      absolute(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
{
    result := false;

    if |numbers| < 2 {
        return;
    }

    for i := 0 to |numbers| - 1
        invariant 0 <= i < |numbers|
        invariant forall k, l :: 0 <= k < i && 0 <= l < |numbers| && k != l ==> absolute(numbers[k] - numbers[l]) >= threshold
    {
        for j := 0 to |numbers| - 1
            invariant 0 <= j < |numbers|
            invariant forall k :: 0 <= k < j && k != i ==> absolute(numbers[i] - numbers[k]) >= threshold
        {
            if i != j && absolute(numbers[i] - numbers[j]) < threshold {
                result := true;
                break;
            }
        }
        if (result) {
            break;
        }
    }
}
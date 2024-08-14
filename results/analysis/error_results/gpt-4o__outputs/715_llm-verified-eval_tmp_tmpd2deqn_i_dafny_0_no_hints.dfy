function abs_real(x: real): real
{
  if x < 0.0 then -x else x
}

method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs_real(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
{
    result := false;

    if |numbers| <= 1 {
        return;
    }

    for i := 0 to |numbers| - 1
        invariant 0 <= i <= |numbers| - 1
        invariant !result ==> forall i0, j0 :: (0 <= i0 < i && 0 <= j0 < |numbers| && i0 != j0 ==> abs_real(numbers[i0] - numbers[j0]) >= threshold)
    {
        for j := i + 1 to |numbers|
            invariant 0 <= j <= |numbers|
            invariant !result ==> forall i0, j0 :: (0 <= i0 <= i && 0 <= j0 < j && i0 != j0 ==> abs_real(numbers[i0] - numbers[j0]) >= threshold)
        {
            if abs_real(numbers[i] - numbers[j]) < threshold {
                result := true;
                return;
            }
        }
    }
}
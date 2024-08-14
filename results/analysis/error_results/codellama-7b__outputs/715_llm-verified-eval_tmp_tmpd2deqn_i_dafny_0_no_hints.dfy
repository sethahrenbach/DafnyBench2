
function abs(x: real): real
{
  if x < 0.0 then -x else x
}

method has_close_elements(numbers: seq<real>, threshold: real) returns (result: bool)
    ensures result <==> exists i, j ::
      0 <= i < |numbers| &&
      0 <= j < |numbers| &&
      i != j &&
      abs(numbers[i] - numbers[j]) < threshold
    ensures result ==> |numbers| > 1
{
    // Loop invariant:
    //   - For all i, j: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j ==> abs(numbers[i] - numbers[j]) >= threshold
    //   - For all i: 0 <= i < |numbers| ==> |numbers| > 1
    //   - For all i: 0 <= i < |numbers| ==> exists j: 0 <= j < |numbers| && i != j ==> abs(numbers[i] - numbers[j]) >= threshold

    // Assertion:
    //   - For all i, j: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j ==> abs(numbers[i] - numbers[j]) >= threshold

    result := false;

    // Loop body:
    for i := 0 to |numbers|
                   forall j0 :: (0 <= j0 < |numbers| ==>
                   (i0 != j0 ==>
                   abs(numbers[i0] - numbers[j0]) >= threshold))))
    {
        for j := 0 to |numbers|
                        forall j0 :: (0 <= j0 < |numbers| ==>
                        (i0 != j0 ==>
                        abs(numbers[i0] - numbers[j0]) >= threshold))))
        {
            if i != j && abs(numbers[i] - numbers[j]) < threshold {
                result := true;
                return;
            }

        }
    }
}

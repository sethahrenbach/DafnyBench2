
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
    var i: int := 0;
    var j: int := 0;

    assert forall i0 :: (0 <= i0 < i ==> forall j0 :: (0 <= j0 < |numbers| ==> absolute(numbers[i0] - numbers[j0]) >= threshold));

    while i < |numbers
    invariant 0 <= i <= |numbers|
    {
        assert forall j0 :: (0 <= j0 < j ==> (i != j0 ==> absolute(numbers[i] - numbers[j0]) >= threshold));

        j := 0;
        while j < |numbers|
        invariant 0 <= j <= |numbers|
        {
            assert forall j0 :: (0 <= j0 < |numbers| ==> (i != j0 ==> absolute(numbers[i] - numbers[j0]) >= threshold));

            if i != j && absolute(numbers[i] - numbers[j]) < threshold {
                result := true;
                return;
            }

            j := j + 1;
        }

        i := i + 1;
    }
}


method AllSequencesEqualLength(sequences: seq<seq<int>>) returns (result: bool)
    ensures result <==> forall i, j :: 0 <= i < |sequences| && 0 <= j < |sequences| ==> |sequences[i]| == |sequences[j]|
    loop invariant 0 <= i <= |sequences|
    loop invariant 0 <= j <= |sequences|
    loop invariant |sequences[i]| == firstLength
    loop invariant |sequences[j]| == firstLength
    loop variant |sequences|
{
    if |sequences| == 0 {
        return true;
    }

    var firstLength := |sequences[0]|;
    result := true;

    for i := 1 to |sequences|
    {
        if |sequences[i]| != firstLength {
            result := false;
            break;
        }
    }
}

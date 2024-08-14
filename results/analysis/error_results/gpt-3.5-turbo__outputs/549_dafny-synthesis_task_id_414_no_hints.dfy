method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
{
    result := false;
    var i: int := 0;
    while i < |seq1|
        invariant 0 <= i <= |seq1|;
        invariant (forall j :: 0 <= j < i ==> seq1[j] not in seq2) <==> !result;
    {
        assert (forall j :: 0 <= j < i :: seq1[j] not in seq2) <==> !result;
        if seq1[i] in seq2 {
            result := true;
            break;
        }
        i := i + 1;
    }
}
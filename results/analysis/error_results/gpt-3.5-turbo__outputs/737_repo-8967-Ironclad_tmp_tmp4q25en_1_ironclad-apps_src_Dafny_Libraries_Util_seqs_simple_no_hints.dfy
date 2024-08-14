
lemma lemma_vacuous_statement_about_a_sequence(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|;
    ensures intseq[0..j]==intseq[..j];
{
    var i := 0;
    while i < j
        invariant 0 <= i <= j;
        invariant intseq[0..i] == intseq[..i];
        decreases j - i;
    {
        i := i + 1;
    }
}

lemma lemma_painful_statement_about_a_sequence(intseq:seq<int>)
    ensures intseq==intseq[..|intseq|];
{
    assert |intseq| == |intseq[..|intseq|]|;
}

lemma lemma_obvious_statement_about_a_sequence(boolseq:seq<bool>, j:int)
    requires 0<=j<|boolseq|-1;
    ensures boolseq[1..][j] == boolseq[j+1];
{
    assert boolseq[1..][j] == boolseq[j+1];
}

lemma lemma_obvious_statement_about_a_sequence_int(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|-1;
    ensures intseq[1..][j] == intseq[j+1];
{
    assert intseq[1..][j] == intseq[j+1];
}

lemma lemma_straightforward_statement_about_a_sequence(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|;
    ensures intseq[..j] + intseq[j..] == intseq;
{
    assert intseq[..j] + intseq[j..] == intseq;
}

lemma lemma_sequence_reduction(s:seq<int>, b:nat)
    requires 0<b<|s|;
    ensures s[0..b][0..b-1] == s[0..b-1];
{
    var t := s[0..b];
    forall (i | 0<=i<b-1)
        invariant 0 <= i < b-1;
        invariant s[0..b][0..b-1][i] == s[0..b-1][i];
        decreases b - 1 - i;
    {
        assert s[0..b][0..b-1][i] == s[0..b-1][i];
    }
}

lemma lemma_seq_concatenation_associative(a:seq<int>, b:seq<int>, c:seq<int>)
    ensures (a+b)+c == a+(b+c);
{
    assert (a+b)+c == a+(b+c);
}

lemma lemma_subseq_concatenation(s: seq<int>, left: int, middle: int, right: int)
    requires 0 <= left <= middle <= right <= |s|;
    ensures s[left..right] == s[left..middle] + s[middle..right];
{
    assert s[left..right] == s[left..middle] + s[middle..right];
}

lemma lemma_seq_equality(a:seq<int>, b:seq<int>, len:int)
    requires |a| == |b| == len;
    requires forall i :: 0 <= i < len ==> a[i] == b[i];
    ensures a == b;
{
    assert a == b;
}

lemma lemma_seq_suffix(s: seq<int>, prefix_length: int, index: int)
    requires 0 <= prefix_length <= index < |s|;
    ensures s[index] == s[prefix_length..][index - prefix_length];
{
    assert s[index] == s[prefix_length..][index - prefix_length];
}

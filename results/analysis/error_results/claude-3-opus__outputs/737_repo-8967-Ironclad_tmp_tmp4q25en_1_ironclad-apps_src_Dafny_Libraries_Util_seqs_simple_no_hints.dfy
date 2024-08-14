lemma lemma_vacuous_statement_about_a_sequence(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|;
    ensures intseq[0..j]==intseq[..j];
{
    // trivially true by definition of seq[..]
}

lemma lemma_painful_statement_about_a_sequence(intseq:seq<int>)
    ensures intseq==intseq[..|intseq|];
{
    // trivially true by definition of seq[..]
}

lemma lemma_obvious_statement_about_a_sequence(boolseq:seq<bool>, j:int)
    requires 0<=j<|boolseq|-1;
    ensures boolseq[1..][j] == boolseq[j+1];
{
    // trivially true by definition of seq[..]
}

lemma lemma_obvious_statement_about_a_sequence_int(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|-1;
    ensures intseq[1..][j] == intseq[j+1];
{
    // trivially true by definition of seq[..]
}

lemma lemma_straightforward_statement_about_a_sequence(intseq:seq<int>, j:int)
    requires 0<=j<|intseq|;
    ensures intseq[..j] + intseq[j..] == intseq;
{
    // prove by induction on j
    if j == 0 {
        // base case
        assert intseq[..0] == [];
        assert intseq[0..] == intseq;
    } else {
        // inductive case
        lemma_straightforward_statement_about_a_sequence(intseq, j-1);
        assert intseq[..j-1] + intseq[j-1..] == intseq;
        assert intseq[..j] == intseq[..j-1] + [intseq[j-1]];
        assert intseq[j..] == intseq[j-1..][1..];
        assert [intseq[j-1]] + intseq[j-1..][1..] == intseq[j-1..];
    }
}

lemma lemma_sequence_reduction(s:seq<int>, b:nat)
    requires 0<b<|s|;
    ensures s[0..b][0..b-1] == s[0..b-1];
{
    var t := s[0..b];
    forall (i | 0<=i<b-1)
        ensures t[0..b-1][i] == t[i];
        ensures s[0..b][i] == s[i];
    {
        assert t[0..b-1][i] == t[i]; // by definition of seq[..]
        assert s[0..b][i] == s[i]; // by definition of seq[..]
    }
}

lemma lemma_seq_concatenation_associative(a:seq<int>, b:seq<int>, c:seq<int>)
    ensures (a+b)+c == a+(b+c);
{
    // prove by induction on |a|
    if |a| == 0 {
        // base case
        assert a == [];
        assert (a+b)+c == b+c;
        assert a+(b+c) == b+c;
    } else {
        // inductive case
        var a' := a[..|a|-1];
        var x := a[|a|-1];
        lemma_seq_concatenation_associative(a', b, c);
        assert (a'+b)+c == a'+(b+c);
        assert (a+b)+c == (a'+[x])+b+c == a'+(b+c)+[x] == (a'+b)+c;
        assert a+(b+c) == a'+(b+c)+[x] == a+(b+c);
    }
}

lemma lemma_subseq_concatenation(s: seq<int>, left: int, middle: int, right: int)
    requires 0 <= left <= middle <= right <= |s|;
    ensures s[left..right] == s[left..middle] + s[middle..right];
{
    // prove by induction on right-middle
    if middle == right {
        // base case
        assert s[middle..right] == s[right..right] == [];
        assert s[left..middle] + [] == s[left..middle];
    } else {
        // inductive case
        lemma_subseq_concatenation(s, left, middle, right-1);
        assert s[left..right-1] == s[left..middle] + s[middle..right-1];
        assert s[left..right] == s[left..right-1] + [s[right-1]];
        assert s[middle..right] == s[middle..right-1] + [s[right-1]];
    }
}

lemma lemma_seq_equality(a:seq<int>, b:seq<int>, len:int)
    requires |a| == |b| == len;
    requires forall i | 0 <= i < len :: a[i] == b[i];
    ensures a == b;
{
    // prove by induction on len
    if len == 0 {
        // base case
        assert a == [];
        assert b == [];
    } else {
        // inductive case
        var a' := a[..|a|-1];
        var b' := b[..|b|-1];
        lemma_seq_equality(a', b', len-1);
        assert a' == b';
        assert a[|a|-1] == b[|b|-1]; // by precondition
        assert a == a' + [a[|a|-1]];
        assert b == b' + [b[|b|-1]];
    }
}

lemma lemma_seq_suffix(s: seq<int>, prefix_length: int, index: int) 
    requires 0 <= prefix_length <= index < |s|;
    ensures s[index] == s[prefix_length..][index - prefix_length];
{
    // prove by induction on index-prefix_length
    if prefix_length == index {
        // base case
        assert s[prefix_length..][0] == s[prefix_length];
    } else {
        // inductive case
        lemma_seq_suffix(s, prefix_length, index-1);
        assert s[index-1] == s[prefix_length..][index-1-prefix_length];
        assert s[prefix_length..][index-prefix_length] == s[index];
    }
}
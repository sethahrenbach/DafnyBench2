
lemma max(a:int, b:int) returns (m:int)
    ensures m >= a
    ensures m >= b
    ensures m == a || m == b
{
    if (a > b) {
        m := a;
    } else {
        m := b;
    }
}

predicate post_max(a:int, b:int, m:int)
{
    m >= a && m >= b && (m == a || m == b)
}

lemma max_loop_invariant(a:int, b:int, m:int)
    ensures a <= b ==> (m == b ==> post_max(a, b, m))
    ensures a <= b ==> (m == a ==> post_max(a, b, m))
{
    if (a > b) {
        assert m == a;
    } else {
        assert m == b;
    }
}

lemma max_deterministic(a:int, b:int, m:int, m':int)
    requires post_max(a, b, m)
    requires post_max(a, b, m')
    ensures m == m'
{}

lemma max_deterministic'(a:int, b:int, m:int, m':int)
    requires m != m'
    ensures !post_max(a, b, m) || !post_max(a, b, m')
{}

lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6Helper<T>(
        s: seq<int>,
        b: int,
        i: nat
    )
    requires |s| > i 
    requires b == s[i]
    ensures s[..i] + [b] == s[..i+1]
    {  }

lemma multisetEquality(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
   requires m1 > m2 + m3
   requires m1 == m2 + m4
   ensures m3 < m4
{
}

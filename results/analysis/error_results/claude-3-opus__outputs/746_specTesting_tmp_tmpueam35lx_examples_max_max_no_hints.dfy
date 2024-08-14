lemma max(a:int, b:int) returns (m:int)
    ensures m >= a
    ensures m >= b
    ensures m == a || m == b
{
    if (a > b) {
        m := a;
        assert m >= a;
        assert m >= b;
        assert m == a;
    } else {
        m := b;
        assert m >= a;
        assert m >= b;
        assert m == b;
    }
}

predicate post_max(a:int, b:int, m:int)
{
    && m >= a
    && m >= b
    && (m == a || m == b)
}

// to check if it is functioning: postcondition not too accommodating
// the case it will refuse
lemma post_max_point_1(a:int, b:int, m:int)
    requires a > b
    requires m != a
    ensures !post_max(a, b, m)
{
    assert m < a || m < b || (m != a && m != b);
}

// an equivalent way of doing so
lemma post_max_point_1'(a:int, b:int, m:int)
    requires a > b
    requires post_max(a, b, m)
    ensures m == a
{
    assert m >= a && m >= b && (m == a || m == b);
    assert m == a;
}

lemma post_max_point_2(a:int, b:int, m:int)
    requires a == b
    requires m != a || m != b
    ensures !post_max(a, b, m)
{
    assert m < a || m < b || (m != a && m != b);
}

lemma post_max_point_3(a:int, b:int, m:int)
    requires a < b
    requires m != b
    ensures !post_max(a, b, m)
{
    assert m < a || m < b || (m != a && m != b);
}

lemma post_max_vertical_1(a:int, b:int, m:int)
    requires m != a && m != b
    ensures !post_max(a, b, m)
{
    assert m < a || m < b || (m != a && m != b);
}

lemma post_max_vertical_1'(a:int, b:int, m:int)
    requires post_max(a, b, m)
    ensures m == a || m == b
{
    assert m >= a && m >= b && (m == a || m == b);
}

// to check if it is implementable
lemma post_max_realistic_1(a:int, b:int, m:int)
    requires a > b
    requires m == a
    ensures post_max(a, b, m)
{
    assert m >= a && m >= b && m == a;
}

lemma post_max_realistic_2(a:int, b:int, m:int)
    requires a < b
    requires m == b
    ensures post_max(a, b, m)
{
    assert m >= a && m >= b && m == b;
}

lemma post_max_realistic_3(a:int, b:int, m:int)
    requires a == b
    requires m == a
    ensures post_max(a, b, m)
{
    assert m >= a && m >= b && m == a;
}


// this form is more natural
lemma max_deterministic(a:int, b:int, m:int, m':int)
    // should include preconditions if applicable
    requires post_max(a, b, m)
    requires post_max(a, b, m')
    ensures m == m'
{
    if (a > b) {
        post_max_point_1'(a, b, m);
        post_max_point_1'(a, b, m');
    } else if (a < b) {
        post_max_point_3(a, b, m);
        post_max_point_3(a, b, m');
    } else {
        assert a == b;
        post_max_realistic_3(a, b, m);
        post_max_realistic_3(a, b, m');
    }
}

lemma max_deterministic'(a:int, b:int, m:int, m':int)
    requires m != m'
    ensures !post_max(a, b, m) || !post_max(a, b, m')
{
    if (post_max(a, b, m) && post_max(a, b, m')) {
        max_deterministic(a, b, m, m');
        assert false;  // contradiction
    }
}



lemma lemmaInvTheProposerOfAnyValidBlockInAnHonestBlockchailnIsInTheSetOfValidatorsHelper6Helper<T>(
        s: seq<int>,
        b: int,
        i: nat
    )
    requires |s| > i 
    requires b == s[i]
    ensures s[..i] + [b] == s[..i+1]
{
    assert s[..i] + [b] == s[..i] + [s[i]];
    assert s[..i] + [s[i]] == s[..i+1];
}

lemma multisetEquality(m1:multiset<int>, m2:multiset<int>, m3:multiset<int>, m4:multiset<int>)
   requires m1 > m2 + m3
   requires m1 == m2 + m4
   ensures m3 < m4
{
    assert m1 > m2 + m3;
    assert m1 == m2 + m4;
    assert m2 + m4 > m2 + m3;
    assert m4 > m3;
}
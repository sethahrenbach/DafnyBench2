
lemma {:induction false} Divby2(n: nat)
    requires n >= 0
    ensures (n*(n-1))%2 == 0
{
    if n == 0 {
        assert 0*(0-1)%2 == 0; // 0*(0-1)%2 == 0
    } else {
        Divby2(n - 1); // proved in case n - 1
        assert (n-1)*(n-2)%2 == 0; // (n-1)*(n-2)%2 == 0
    }
}

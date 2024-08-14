// verifies
function expo(x:int, n:nat): int
requires n >= 0;
{
    if (n == 0) then 1
    else x * expo(x, n - 1)
}

lemma {:induction false} Expon23(n: nat)
requires n >= 0;
ensures ((expo(2, 3 * n) - expo(3, n))) % 5 == 0;
{
    if (n == 0) { 
        assert expo(2, 3 * 0) - expo(3, 0) == 1 - 1;
        assert (expo(2, 3 * 0) - expo(3, 0)) % 5 == 0;
    } else if (n == 1) {
        assert expo(2, 3 * 1) - expo(3, 1) == 8 - 3;
        assert (expo(2, 3 * 1) - expo(3, 1)) % 5 == 0;
    } else {
        Expon23(n - 1);
        assert (expo(2, 3 * (n - 1)) - expo(3, (n - 1))) % 5 == 0;
        assert expo(2, 3 * n) == expo(2, 3 * (n - 1)) * 8;
        assert expo(3, n) == expo(3, n - 1) * 3;
        assert (expo(2, 3 * n) - expo(3, n)) == (expo(2, 3 * (n - 1)) * 8 - expo(3, n - 1) * 3);
        assert (expo(2, 3 * n) - expo(3, n)) % 5 == ((expo(2, 3 * (n - 1)) * 8 - expo(3, n - 1) * 3) % 5);
        assert ((expo(2, 3 * (n - 1)) * 8 - expo(3, n - 1) * 3) % 5) == 0;
        assert (expo(2, 3 * n) - expo(3, n)) % 5 == 0; // Directly asserting the final result
    }
}

method check() {
}
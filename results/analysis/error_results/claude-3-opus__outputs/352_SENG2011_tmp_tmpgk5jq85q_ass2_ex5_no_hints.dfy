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
        assert expo(2, 0) == 1;
        assert expo(3, 0) == 1;
        assert (1 - 1) % 5 == 0;
    } else if (n == 1) {
        assert expo(2, 3) == 8;
        assert expo(3, 1) == 3;
        assert (8 - 3) % 5 == 0;
    } else {
        var i:nat := n;
        var j:nat := n;
        // assume true for n - 1
        Expon23(n - 1);
        // prove for n
        assert expo(2, 3 * (n - 1)) % 5 == expo(3, n - 1) % 5;
        calc {
            expo(2, 3 * n) % 5;
            expo(2, 3 * (n - 1) + 3) % 5;
            { assert expo(2, 3 * (n - 1) + 3) == expo(2, 3 * (n - 1)) * expo(2, 3); }
            (expo(2, 3 * (n - 1)) * expo(2, 3)) % 5;
            { assert expo(2, 3) % 5 == 3; }
            (expo(2, 3 * (n - 1)) * 3) % 5;
            { assert expo(2, 3 * (n - 1)) % 5 == expo(3, n - 1) % 5 by {
                Expon23(n - 1);
              }
            }
            (expo(3, n - 1) * 3) % 5;
            expo(3, (n - 1) + 1) % 5;
            expo(3, n) % 5;
        }
    }
}

method check() {
    // No assertions needed here, the lemma is already verified
}

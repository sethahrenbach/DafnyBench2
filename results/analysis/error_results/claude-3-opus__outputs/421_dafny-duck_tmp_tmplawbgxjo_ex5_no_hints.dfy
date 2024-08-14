// program verifies
function expo(x:int, n:nat): int
{
    if n == 0 then 1
    else x * expo(x, n-1)
}

lemma {:induction false} Expon23(n: nat)
requires n >= 0
ensures ((expo(2,3*n) - expo(3,n)) % (2+3)) == 0
{   
    // base case
    if (n == 0) {
        assert expo(2,3*0) == 1;
        assert expo(3,0) == 1;
        assert ((1 - 1) % 5) == 0;
    }
    else if (n == 1) {
        assert expo(2,3*1) == 8;
        assert expo(3,1) == 3;
        assert ((8 - 3) % 5) == 0;
    }
    else {
        Expon23(n-1); // lemma proved for case n-1  
        
        assert expo(2,3*n) == 8 * expo(2,3*(n-1));
        assert expo(3,n) == 3 * expo(3,n-1);

        assert ((expo(2,3*(n-1)) - expo(3,n-1)) % 5) == 0; // from induction hypothesis
        
        calc == {
            ((expo(2,3*n) - expo(3,n)) % 5);
            ((8*expo(2,3*(n-1)) - 3*expo(3,n-1)) % 5);
            {
                assert expo(2,3*(n-1)) % 5 == expo(3,n-1) % 5;
                assert (8*expo(2,3*(n-1))) % 5 == (8*expo(3,n-1)) % 5;
                assert (8*expo(3,n-1)) % 5 == (-2*expo(3,n-1)) % 5;
            }
            ((-2*expo(3,n-1) - 3*expo(3,n-1)) % 5);
            (-5*expo(3,n-1) % 5);
            {
                assert expo(3,n-1) % 5 == expo(2,3*(n-1)) % 5;
                assert expo(2,3*(n-1)) % 5 == expo(2,3*n) % 5;
                assert expo(2,3*n) % 5 == expo(3,n) % 5;
                assert expo(3,n-1) % 5 == expo(3,n) % 5;
            }
            (-5*expo(3,n) % 5);
            0;
        }
    }
}
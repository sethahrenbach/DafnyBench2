/**
CVS 2021-22 Handout 1
Authors
Gonçalo Martins Lourenço nº55780
Joana Soares Faria  nº55754
 */

// First Exercise
lemma peasantMultLemma(a:int, b:int)
    requires b >= 0
    ensures b % 2 == 0 ==> (a * b == 2 * a * b / 2)
    ensures b % 2 == 1 ==> (a * b == a + 2 * a * (b - 1) / 2)
    {
        if (b % 2 == 0 && b > 0) { 
            peasantMultLemma(a, b - 2);
        }

        if (b % 2 == 1 && b > 1) {
            peasantMultLemma(a, b - 2);
        }
    }

method peasantMult(a: int, b: int) returns (r: int)
    requires b > 0
    ensures r == a * b
    {
        r := 0;
        var aa := a;
        var bb := b;
    
        while(bb > 0)
        invariant r + aa * bb == a * b
        invariant bb >= 0
        decreases bb
        { 
            // Use of lemma was not necessary for a successful verification
            // peasantMultLemma(aa, bb);
            if (bb % 2 == 0)
            {
                aa := 2 * aa;
                bb := bb / 2;
            } else
            {
                r := r + aa;
                aa := 2 * aa;
                bb := (bb-1) / 2;
            }
        } 
    }


//Second Exercise
method euclidianDiv(a: int,b : int) returns (q: int,r: int)
    requires a >= 0
    requires b > 0
    ensures a == b * q + r
    {
        r := a;
        q := 0;
        while(r >= b)
        invariant a == b * q + r
        invariant 0 <= r
        {
            ghost var oldr := r;
            r := r - b;
            q := q + 1;
            assert oldr > r;
        }
    }
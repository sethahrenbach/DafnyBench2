module RussianMultiplication {
    
    export provides mult

    method mult(n0 : int, m0 : int) returns (res : int)
    ensures res == (n0 * m0);
    {
        var n, m : int;
        res := 0;
        if (n0 >= 0) {
            n,m := n0, m0;
        } 
        else {
            n,m := -n0, -m0;
        }
        while (n > 0)
        invariant 0 <= n <= n0;
        invariant res == (n0 - n) * m0 + (n * m0);
        decreases n;
        {
            res := res + m; 
            n := n - 1; 
        }
        assert res == n0 * m0;
    }
}
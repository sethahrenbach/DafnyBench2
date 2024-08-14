
module Math__div_def_i {
    /*
    function mod(x:int, m:int) : int
        requires m > 0;
    {
        if x < 0 then
            mod(m + x, m)
        else if x < m then
            x
        else
            mod(x - m, m)
    }
    */

    function div(x:int, d:int) : int
        requires d != 0;
        ensures div(x, d) == x / d;
    {
        x/d
    }

    function mod(x:int, d:int) : int
        requires d != 0;
        ensures mod(x, d) == x % d;
    {
        x%d
    }

    function div_recursive(x:int, d:int) : int
        requires d != 0;
        ensures div_recursive(x, d) == x / d;
    {
        if d > 0 {
            INTERNAL_div_recursive(x, d, 0)
        } else {
            INTERNAL_div_recursive(x, -d, 0)
        }
    }

    function mod_recursive(x:int, d:int) : int
        requires d > 0;
        ensures mod_recursive(x, d) == x % d;
    {
        if x >= 0 {
            INTERNAL_mod_recursive(x, d, 0)
        } else {
            INTERNAL_mod_recursive(-x, d, 0)
        }
    }

    function mod_boogie(x:int, y:int) : int
        requires y != 0;
        ensures mod_boogie(x, y) == x % y;
    {
        x % y //- INTERNAL_mod_boogie(x,y) 
    }

    function div_boogie(x:int, y:int) : int
        requires y != 0;
        ensures div_boogie(x, y) == x / y;
    {
        x / y //-{ INTERNAL_div_boogie(x,y) }
    }

    function my_div_recursive(x:int, d:int) : int
        requires d != 0;
        ensures my_div_recursive(x, d) == x / d;
    {
        if d > 0 {
            my_div_pos(x, d)
        } else {
            -1 * my_div_pos(x, -d)
        }
    }

    function my_div_pos(x:int, d:int) : int
        requires d >  0;
        ensures my_div_pos(x, d) == x / d;
    {
        if x < 0 {
            -1 + my_div_pos(x+d, d)
        } else if x < d {
            0
        } else {
            1 + my_div_pos(x-d, d)
        }
    }

    function my_mod_recursive(x:int, m:int) : int
        requires m > 0;
        ensures my_mod_recursive(x, m) == x % m;
    {
        if x < 0 {
            my_mod_recursive(m + x, m)
        } else if x < m {
            x
        } else {
            my_mod_recursive(x - m, m)
        }
    }

    function INTERNAL_div_recursive(x:int, d:int, acc:int) : int
        requires d != 0;
        ensures INTERNAL_div_recursive(x, d, acc) == x / d + acc;
        ensures acc + (x / d) * d == x;
    {
        if acc >= x {
            acc
        } else {
            INTERNAL_div_recursive(x, d, acc + d)
        }
    }

    function INTERNAL_mod_recursive(x:int, m:int, acc:int) : int
        requires m > 0;
        ensures INTERNAL_mod_recursive(x, m, acc) == x % m;
        ensures acc < m;
    {
        if acc + m > x {
            x - acc
        } else {
            INTERNAL_mod_recursive(x, m, acc + m)
        }
    }

    /*
    ghost method mod_test()
    {
    }
    */

}

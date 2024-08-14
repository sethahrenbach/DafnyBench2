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
    ensures x == d * result + mod(x, d);
{
    x / d
}

function mod(x:int, d:int) : int
    requires d != 0;
    ensures 0 <= result < if d < 0 then -d else d;
    ensures x == d * div(x, d) + result;
{
    x % d
}

function div_recursive(x:int, d:int) : int
    requires d != 0;
    ensures x == d * result + mod_recursive(x, d);
{
    INTERNAL_div_recursive(x, d)
}

function mod_recursive(x:int, d:int) : int
    requires d > 0;
    ensures 0 <= result < d;
    ensures x == d * div_recursive(x, d) + result;
{
    INTERNAL_mod_recursive(x, d)
}

function mod_boogie(x:int, y:int) : int
    requires y != 0;
    ensures 0 <= result < if y < 0 then -y else y;
    ensures x == y * div_boogie(x, y) + result;
{
    x % y
}

function div_boogie(x:int, y:int) : int
    requires y != 0;
    ensures x == y * result + mod_boogie(x, y);
{
    x / y
}

function my_div_recursive(x:int, d:int) : int
    requires d != 0;
    ensures x == d * result + my_mod_recursive(x, if d < 0 then -d else d);
{
    if d > 0 then
        my_div_pos(x, d)
    else
        -1 * my_div_pos(x, -1 * d)
}

function my_div_pos(x:int, d:int) : int
    requires d > 0;
    ensures x == d * result + my_mod_recursive(x, d);
{
    if x < 0 then
        -1 + my_div_pos(x + d, d)
    else if x < d then
        0
    else
        1 + my_div_pos(x - d, d)
}

function my_mod_recursive(x:int, m:int) : int
    requires m > 0;
    ensures 0 <= result < m;
    ensures x == m * my_div_recursive(x, m) + result;
{
    if x < 0 then
        my_mod_recursive(m + x, m)
    else if x < m then
        x
    else
        my_mod_recursive(x - m, m)
}


//- Kept for legacy reasons:
//-static function INTERNAL_mod_boogie(x:int, m:int) : int   { x % y }
function INTERNAL_mod_recursive(x:int, m:int) : int  
    requires m > 0;
    ensures 0 <= result < m;
    ensures x == m * INTERNAL_div_recursive(x, m) + result;
{
    my_mod_recursive(x, m)
}

//-static function INTERNAL_div_boogie(x:int, m:int) : int   { x / m }
function INTERNAL_div_recursive(x:int, d:int) : int 
    requires d != 0;
    ensures x == d * result + INTERNAL_mod_recursive(x, if d < 0 then -d else d);
{
    my_div_recursive(x, d)
}


/*
ghost method mod_test()
{
}
*/

}
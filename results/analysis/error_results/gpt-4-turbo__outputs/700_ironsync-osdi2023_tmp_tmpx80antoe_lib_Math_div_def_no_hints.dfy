module Math__div_def_i {

function div(x:int, d:int) : int
    requires d != 0;
{
    x/d
}

function mod(x:int, d:int) : int
    requires d != 0;
{
    x%d
}

function div_recursive(x:int, d:int) : int
    requires d != 0;
{ INTERNAL_div_recursive(x,d) }

function mod_recursive(x:int, d:int) : int
    requires d > 0;
{ INTERNAL_mod_recursive(x,d) }

function mod_boogie(x:int, y:int) : int
    requires y != 0;
{ x % y }

function div_boogie(x:int, y:int) : int
    requires y != 0;
{ x / y }

function my_div_recursive(x:int, d:int) : int
    requires d != 0;
{
    if d > 0 then
        my_div_pos(x, d)
    else
        -1 * my_div_pos(x, -d)
}

function my_div_pos(x:int, d:int) : int
    requires d > 0;
    decreases x < 0 ? -x : x;
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
    decreases x < 0 ? -x : x;
{
    if x < 0 then
        my_mod_recursive(m + x, m)
    else if x < m then
        x
    else
        my_mod_recursive(x - m, m)
}

function INTERNAL_mod_recursive(x:int, m:int) : int  
    requires m > 0;
{ my_mod_recursive(x, m) }

function INTERNAL_div_recursive(x:int, d:int) : int 
    requires d != 0;
{ my_div_recursive(x, d) }

}

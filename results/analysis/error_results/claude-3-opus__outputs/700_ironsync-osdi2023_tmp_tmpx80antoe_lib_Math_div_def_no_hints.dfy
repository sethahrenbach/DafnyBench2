//- Specs/implements mathematical div and mod, not the C version.
//- This may produce "surprising" results for negative values
//- For example, -3 div 5 is -1 and -3 mod 5 is 2.
//- Note this is consistent: -3 * -1 + 2 == 5

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
    ensures my_div_recursive(x,d) == div(x,d);
{
    if d > 0 then
        my_div_pos(x, d)
    else
        -1 * my_div_pos(x, -1*d)
}

lemma my_div_pos_lemma(x:int, d:int)
    requires d > 0;
    ensures my_div_pos(x,d) == div(x,d);
    decreases if x < 0 then -x else x;
{
    if x < 0 {
        my_div_pos_lemma(x+d, d);
    } else if x >= d {
        my_div_pos_lemma(x-d, d);
    }
}

function my_div_pos(x:int, d:int) : int
    requires d >  0;
    ensures my_div_pos(x,d) == div(x,d);
{
    if x < 0 then
        -1 + my_div_pos(x+d, d)
    else if x < d then
        0
    else
        1 + my_div_pos(x-d, d)
}

lemma my_mod_recursive_lemma(x:int, m:int)
    requires m > 0;
    ensures my_mod_recursive(x,m) == mod(x,m);
    decreases if x < 0 then m+x else x;
{
    if x < 0 {
        my_mod_recursive_lemma(m+x, m);
    } else if x >= m {
        my_mod_recursive_lemma(x-m, m);
    }
}

function my_mod_recursive(x:int, m:int) : int
    requires m > 0;
    ensures my_mod_recursive(x,m) == mod(x,m);
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
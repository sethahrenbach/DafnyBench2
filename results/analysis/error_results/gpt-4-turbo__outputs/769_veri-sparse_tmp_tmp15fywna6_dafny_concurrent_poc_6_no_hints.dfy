
class Process {
    var row: nat;
    var curColumn: nat;
    var opsLeft: nat;

    constructor (init_row: nat, initOpsLeft: nat) 
        ensures row == init_row
        ensures opsLeft == initOpsLeft
        ensures curColumn == 0
    {
        row := init_row;
        curColumn := 0;
        opsLeft := initOpsLeft;
    }
}

function sum(s: seq<nat>): nat
    ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
{
    if s == [] then 0 else s[0] + sum(s[1..])
}

lemma sum0(s: seq<nat>)
    ensures sum(s) == 0 ==> forall i :: 0 <= i < |s| ==> s[i] == 0
{
    if s == [] {
    } else {
        sum0(s[1..]);
    }
}

lemma sum_const(s: seq<nat>, x: nat)
    ensures (forall i :: 0 <= i < |s| ==> s[i] == x) ==> sum(s) == |s| * x 
{
    if |s| > 0 {
        sum_const(s[1..], x);
    }
}

lemma sum_eq(s1: seq<nat>, s2: seq<nat>)
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[i]
    ensures sum(s1) == sum(s2)
{
    if |s1| > 0 {
        sum_eq(s1[1..], s2[1..]);
    }
}

lemma sum_exept(s1: seq<nat>, s2: seq<nat>, x: nat, j: nat)
    requires |s1| == |s2|
    requires j < |s1|
    requires forall i :: 0 <= i < |s1| ==> i != j ==> s1[i] == s2[i]
    requires s1[j] == s2[j] + x
    ensures sum(s1) == sum(s2) + x
{
    if s1 == [] {
    } else {
        if j == 0 {
            sum_eq(s1[1..], s2[1..]);
        } else {
            sum_exept(s1[1..], s2[1..], x, j - 1);
        }
    }
}

function calcRow(M: array2<int>, x: seq<int>, row: nat, start_index: nat): int
    reads M
    requires M.Length1 == |x|
    requires row < M.Length0
    requires start_index <= M.Length1
{
    if start_index == M.Length1 then
        0
    else
        M[row, start_index] * x[start_index] + calcRow(M, x, row, start_index + 1)
}

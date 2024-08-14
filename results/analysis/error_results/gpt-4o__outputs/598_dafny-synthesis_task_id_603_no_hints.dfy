method LucidNumbers(n: int) returns (lucid: seq<int>)
    requires n >= 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] % 3 == 0
    ensures forall i :: 0 <= i < |lucid| ==> lucid[i] <= n
    ensures forall i, j :: 0 <= i < j < |lucid| ==> lucid[i] < lucid[j]
{
    lucid := [];
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant forall j :: 0 <= j < |lucid| ==> lucid[j] % 3 == 0
        invariant forall j :: 0 <= j < |lucid| ==> lucid[j] <= n
        invariant forall j, k :: 0 <= j < k < |lucid| ==> lucid[j] < lucid[k]
        invariant |lucid| <= (i + 2) / 3
    {
        if i % 3 == 0 {
            assert forall j :: 0 <= j < |lucid| ==> lucid[j] < i;
            lucid := lucid + [i];
        }
        i := i + 1;
    }
}
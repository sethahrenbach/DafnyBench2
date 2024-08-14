function reverse(xs: seq<nat>): seq<nat>
    ensures |reverse(xs)| == |xs| && (∀i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1])
{
    if xs == [] {
        []
    } else {
        reverse(xs[1..]) + [xs[0]]
    }
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
    ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if xs == [] {
        calc {
            reverse([] + ys);
            calc {
                [] + ys;
                ys;
            }
            reverse(ys);
            reverse(ys) + reverse([]);
        }
    } else {
        var zs := xs + ys;
        ReverseAppendDistr(xs[1..], ys);
    }
}

lemma ReverseInvolution(xxs: seq<nat>)
    ensures reverse(reverse(xxs)) == xxs
{
    if xxs == [] {
    } else {
        calc {
            reverse(reverse(xxs));
            ==
            reverse(reverse(xxs[1..]) + [xxs[0]]);
            ==
            { ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]); }
            reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
            ==
            { ReverseInvolution(xxs[1..]); }
            calc {
                reverse([xxs[0]]);
                ==
                [] + [xxs[0]];
                ==
                [xxs[0]];
            }
            [xxs[0]] + reverse(xxs[1..]);
            ==
            xxs;
        }
    }
}
function reverse(xs: seq<nat>): seq<nat>
{
    if xs == [] then [] else reverse(xs[1..]) + [xs[0]]
}

lemma ReverseAppendDistr(xs: seq<nat>, ys: seq<nat>)
ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
{
    if xs == [] {
        calc {
            reverse([] + ys);
            == { assert [] + ys == ys; }
            reverse(ys);
            == { assert reverse([]) == []; }
            reverse(ys) + [];
            == { assert [] == reverse([]); }
            reverse(ys) + reverse(xs);
        }
    } else {
        calc {
            reverse(xs + ys);
            == { assert xs != []; }
            reverse((xs[1..] + [xs[0]]) + ys);
            == { assert (xs[1..] + [xs[0]]) + ys == xs[1..] + ([xs[0]] + ys); }
            reverse(xs[1..] + ([xs[0]] + ys));
            == { ReverseAppendDistr(xs[1..], [xs[0]] + ys); }
            reverse([xs[0]] + ys) + reverse(xs[1..]);
            == { ReverseAppendDistr([xs[0]], ys); }
            reverse(ys) + reverse([xs[0]]) + reverse(xs[1..]);
            == { assert reverse([xs[0]]) == [xs[0]]; }
            reverse(ys) + [xs[0]] + reverse(xs[1..]);
            == { assert [xs[0]] + reverse(xs[1..]) == reverse(xs); }
            reverse(ys) + reverse(xs);
        }
    }
}

lemma ReverseInvolution(xxs: seq<nat>)
ensures reverse(reverse(xxs)) == xxs
{
    if xxs == [] {
        calc {
            reverse(reverse([]));
            == { assert reverse([]) == []; }
            reverse([]);
            == { assert reverse([]) == []; }
            [];
            == { assert [] == xxs; }
            xxs;
        }
    } else {
        calc {
            reverse(reverse(xxs));
            == { assert xxs != []; }
            reverse(reverse(xxs[1..]) + [xxs[0]]);
            == { ReverseAppendDistr(reverse(xxs[1..]), [xxs[0]]); }
            reverse([xxs[0]]) + reverse(reverse(xxs[1..]));
            == { ReverseInvolution(xxs[1..]); }
            reverse([xxs[0]]) + xxs[1..];
            == { assert reverse([xxs[0]]) == [xxs[0]]; }
            [xxs[0]] + xxs[1..];
            == { assert [xxs[0]] + xxs[1..] == xxs; }
            xxs;
        }
    }
}
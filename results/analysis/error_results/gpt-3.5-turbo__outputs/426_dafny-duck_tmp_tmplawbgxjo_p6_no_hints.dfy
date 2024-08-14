
const vowels: set<char> := {'a', 'e', 'i', 'o', 'u'}

function FilterVowels(xs: seq<char>): seq<char>
    ensures forall i :: 0 <= i < |xs| ==> xs[i] in vowels <==> result[i] in vowels
{
    if |xs| == 0 then []
    else if xs[|xs|-1] in vowels then FilterVowels(xs[..|xs|-1]) + [xs[|xs|-1]]
    else FilterVowels(xs[..|xs|-1])
}

method FilterVowelsArray(xs: array<char>) returns (ys: array<char>)
    ensures fresh(ys)
    ensures FilterVowels(xs[..]) == ys[..]
{
    var n := 0;
    var i := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant n == CountVowels(xs, 0, i)
    {
        if xs[i] in vowels {
            n := n + 1;
        }
        i := i + 1;
    }

    ys := new char[n];
    i := 0;
    var j := 0;
    while i < xs.Length
        invariant 0 <= i <= xs.Length
        invariant 0 <= j <= n
        invariant n == CountVowels(xs, 0, i)
        invariant j == CountVowels(ys, 0, j)
        invariant forall k :: 0 <= k < i ==> xs[k] in vowels <==> ys[CountVowels(xs, 0, k)] in vowels
    {
        if xs[i] in vowels {
            ys[j] := xs[i];
            j := j + 1;
        }
        i := i + 1;
    }
}

function CountVowels(xs: array<char>, start: int, end: int): int
    ensures 0 <= result <= end - start
    ensures result == CountVowelsHelper(xs, start, end, 0)
{
    CountVowelsHelper(xs, start, end, 0)
}

function CountVowelsHelper(xs: array<char>, start: int, end: int, count: int): int
    ensures 0 <= result <= end - start
    ensures result == count + CountVowels(xs, start + count, end)
{
    if start >= end then count
    else if xs[start + count] in vowels {
        CountVowelsHelper(xs, start, end, count + 1)
    } else {
        CountVowelsHelper(xs, start, end, count)
    }
}

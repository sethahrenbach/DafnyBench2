
method UniqueProduct(arr: array<int>) returns (product: int)
    ensures product == SetProduct((set i | 0 <= i < arr.Length :: arr[i]))
{
    var p := 1;
    var seen: set<int> := {};
    
    for i := 0 to arr.Length
        invariant 0 <= i <= arr.Length
        invariant product == SetProduct((set j | 0 <= j < i :: arr[j]))
        invariant p == SetProduct(seen)
        invariant seen == { arr[j] | j in 0..i }
    {
        if ! (arr[i] in seen) {
            seen := seen + { arr[i] };
            p := p * arr[i];
            assert SetProduct(seen) == p;
        }
    }
    product := p;
}

ghost function SetProduct(s: set<int>): int
{
    if s == {} then 1
    else var x:| x in s; 
         x * SetProduct(s - {x})
}

lemma SetProductLemma(s: set<int>, x: int)
    requires x in s
    ensures SetProduct(s - {x}) * x == SetProduct(s)
{
    if s != {}
    {
        var y:| y in s && y * SetProduct(s - {y}) == SetProduct(s);
        if y == x {}
        else {
            calc {
                SetProduct(s);
                y * SetProduct(s - {y});
                { SetProductLemma(s - {y}, x); }
                y * x * SetProduct(s - {y} - {x});
                y * x * SetProduct(s - {x} - {y});
                x * y * SetProduct(s - {x} - {y});
                { SetProductLemma(s - {x}, y); }
                x * SetProduct(s - {x});
            }
        }
    }
}

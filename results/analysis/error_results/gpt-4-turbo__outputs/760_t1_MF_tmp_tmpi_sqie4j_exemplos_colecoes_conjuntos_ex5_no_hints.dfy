function to_seq<T>(a: array<T>, i: int) : (res: seq<T>)
  requires 0 <= i <= a.Length
  ensures res == a[i..]
  reads a
  decreases a.Length - i // Decreases clause to ensure termination
{
  if i == a.Length
    then []
    else [a[i]] + to_seq(a, i + 1)
}

method Main() {
  var a: array<int> := new int[2];
  a[0] := 2;
  a[1] := 3;

  var ms: multiset<int> := multiset(a[..]);
  assert ms == multiset{2, 3}; // Correct assertion to ensure the multiset contains exactly the elements of the array
  assert multiset{a[0], a[1]} == ms; // Correct assertion to ensure the multiset created from the array matches the expected multiset
}

method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
{
  // Loop Invariant: c[..] == a[..] + [b]
  // Precondition: a is an array of integers
  // Precondition: b is an integer
  // Postcondition: c is an array of integers
  // Postcondition: c[..] == a[..] + [b]
  c := new int[a.Length+1];
  var i:= 0;
  while (i < a.Length)
  {
    // Loop Invariant: c[..] == a[..] + [b]
    // Invariant: c[i] == a[i]
    c[i] := a[i];
    i:=i+1;
  }
  // Loop Invariant: c[..] == a[..] + [b]
  // Invariant: c[a.Length] == b
  c[a.Length]:=b;
}

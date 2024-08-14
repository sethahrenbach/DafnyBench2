
method Reverse(a: array<char>) returns (b: array<char>)
  requires a.Length > 0
  ensures a.Length == b.Length
  ensures forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k];
{
  b := new char[a.Length];
  var i:= 0;

  loop invariant 0 <= i <= a.Length-1;
  loop invariant forall k :: 0 <= k < i ==> b[k] == a[(a.Length-1) - k];
  loop invariant forall k :: i <= k < a.Length ==> b[k] == a[(a.Length-1) - k];

  while(i < a.Length)
  {
    b[i] := a[(a.Length-1) - i];
    i := i + 1;
  }

  assert forall k :: 0 <= k < a.Length ==> a[k] == b[(a.Length-1) - k];
}

method Main()
{
  var a := new char[8];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7] := 'd', 'e', 's', 'r', 'e', 'v', 'e', 'r';
  var b := Reverse(a);
  print b[..];

  a := new char[1];
  a[0] := '!';
  b := Reverse(a);
  print b[..], '\n';
}

  I apologize for the confusion. It seems that the previous code had a syntax error. Here is the corrected code:

method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
{
  var splitPoint : int := a.Length / 2;

  b := new int[splitPoint];
  c := new int[a.Length - splitPoint];

  var i : int := 0;

  while (i < splitPoint)
  {
    b[i] := a[i];
    i := i + 1;
  }

  while (i < a.Length)
  {
    c[i] := a[i];
    i := i + 1;
  }

  // postcondition: b[..] + c[..] == a[..]
  assert b[..] + c[..] == a[..];

  // postcondition: b.Length + c.Length == a.Length
  assert b.Length + c.Length == a.Length;

  // postcondition: a.Length > 1 ==> a.Length > b.Length
  assert a.Length > 1 ==> a.Length > b.Length;

  // postcondition: a.Length > 1 ==> a.Length > c.Length
  assert a.Length > 1 ==> a.Length > c.Length;
}

I hope this corrected code meets your requirements.
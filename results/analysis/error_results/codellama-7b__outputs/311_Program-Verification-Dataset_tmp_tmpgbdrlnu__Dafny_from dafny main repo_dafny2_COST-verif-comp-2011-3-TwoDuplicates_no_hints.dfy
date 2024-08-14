
method Search(a: array<int>) returns (p: int, q: int)
  requires 4 <= a.Length;
  requires exists p,q :: p != q && IsDuplicate(a, p) && IsDuplicate(a, q);
  ensures p != q && IsDuplicate(a, p) && IsDuplicate(a, q);
{
  var d := new int[a.Length-2];
  var i := 0;
  while (i < d.Length)
  {
    d[i], i := -1, i+1;
  }

  i, p, q := 0, 0, 1;
  while (true)
  {
    var k := d[a[i]];
    if (k == -1)
    {
      d[a[i]] := i;
    }
    else
    {
      if (p != q)
      {
        p, q := a[i], a[i];
      }
      else
      {
        q := a[i];
        return;
      }
    }
    i := i + 1;
  }
}

function IsDuplicate(a: array<int>, x: int) returns (b: bool)
  requires 0 <= x < a.Length;
  ensures b == (exists y :: 0 <= y < x && a[y] == a[x]);
{
  var i := 0;
  while (i < x)
  {
    if (a[i] == a[x])
    {
      return true;
    }
    i := i + 1;
  }
  return false;
}

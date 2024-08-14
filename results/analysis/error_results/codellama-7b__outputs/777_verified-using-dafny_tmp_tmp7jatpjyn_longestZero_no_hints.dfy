
function getSize(i: int, j: int) : int
{
  j - i + 1
}

method longestZero(a: array<int>) returns (sz: int, pos: int)
  requires 1 <= a.Length
  ensures 0 <= sz <= a.Length
  ensures 0 <= pos < a.Length
  ensures pos + sz <= a.Length
  ensures forall i: int :: pos <= i < pos + sz ==> a[i] == 0
  ensures forall i, j :: (0 <= i < j < a.Length && getSize(i, j) > sz) ==> exists k :: i <= k <= j && a[k] != 0
{
  var b := new int[a.Length];
  var idx := 0;
  while idx < a.Length
  {
    if a[idx] == 0
    {
      b[idx] := 1;
    }
    else
    {
      b[idx] := 0;
    }
    idx := idx + 1;
  }
  sz := b[0];
  pos := 0;
  while idx < a.Length
  {
    if b[idx] > sz
    {
      sz := b[idx];
      pos := idx - b[idx] + 1;
    }
    idx := idx + 1;
  }
}

method Main()
{
  var a := new int[10];
  forall i | 0 <= i < a.Length
    { a[i] := 0;}
  
  var sz, pos := longestZero(a);
  print a[..], "\n";
  print a[pos..(sz+pos)], "\n";
}

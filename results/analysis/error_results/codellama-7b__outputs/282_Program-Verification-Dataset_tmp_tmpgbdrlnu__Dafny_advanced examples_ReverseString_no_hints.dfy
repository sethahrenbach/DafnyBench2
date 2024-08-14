
method yarra(arr : array<char>) returns (outarr : array<char>)
  requires arr != null && arr.Length > 0
  ensures outarr != null && arr.Length == outarr.Length && reversed(arr,outarr)
{
  var i:= 0;
  var j:= arr.Length-1;
  outarr := new char[arr.Length];
  outarr[0] := arr[j];
  i := i+1;
  j := j-1;
  while i<arr.Length && 0<=j<arr.Length
  {
    outarr[i] := arr[j];
    i:=i+1;
    j:=j-1;
  }
  return outarr;
}

function reversed(arr : array<char>, outarr : array<char>) : bool
  requires arr != null && outarr != null && arr.Length == outarr.Length
  ensures arr.Length == outarr.Length && reversed(arr,outarr)
{
  var i:= 0;
  var j:= arr.Length-1;
  while i<arr.Length && 0<=j<arr.Length
  {
    if arr[i] != outarr[j]
      return false;
    i:=i+1;
    j:=j-1;
  }
  return true;
}

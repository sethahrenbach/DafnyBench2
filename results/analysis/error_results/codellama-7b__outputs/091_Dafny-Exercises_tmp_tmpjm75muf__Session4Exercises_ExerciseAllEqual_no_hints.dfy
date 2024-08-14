
method allEqual(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0..v.Length])
{
  var i := 0;
  b := true;
  while (i < v.Length && b) {
    b := v[i] == v[0];
    i := i + 1;
  }
}

method mallEqual1(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0..v.Length])
{
  var i := 0;
  b := true;
  while (i < v.Length && b) {
    b := v[i] == v[0];
    i := i + 1;
  }
}

method mallEqual2(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0..v.Length])
{
  var i := 0;
  b := true;
  while (i < v.Length && b) {
    b := v[i] == v[0];
    i := i + 1;
  }
}

method mallEqual3(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0..v.Length])
{
  var i := 0;
  b := true;
  while (i < v.Length && b) {
    b := v[i] == v[0];
    i := i + 1;
  }
}

method mallEqual4(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0..v.Length])
{
  var i := 0;
  b := true;
  while (i < v.Length && b) {
    b := v[i] == v[0];
    i := i + 1;
  }
}

method mallEqual5(v: array<int>) returns (b: bool)
  ensures b == allEqual(v[0..v.Length])
{
  var i := 0;
  b := true;
  while (i < v.Length && b) {
    b := v[i] == v[0];
    i := i + 1;
  }
}

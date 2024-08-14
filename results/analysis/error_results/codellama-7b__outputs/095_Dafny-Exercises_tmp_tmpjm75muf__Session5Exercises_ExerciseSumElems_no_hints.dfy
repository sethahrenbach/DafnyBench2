
function Sum(s: seq<int>): int
{
  requires s != null;
  requires 0 <= s.Length;
  requires s.Length <= 100;
  ensures 0 <= result <= 100;

  var sum: int := 0;
  for i: int in s do
    sum := sum + i;
  return sum;
}

lemma Sum_correct(s: seq<int>):
  requires s != null;
  requires 0 <= s.Length;
  requires s.Length <= 100;
  ensures 0 <= Sum(s) <= 100;
{
  var sum: int := 0;
  for i: int in s do
    sum := sum + i;
  assert 0 <= sum <= 100;
}

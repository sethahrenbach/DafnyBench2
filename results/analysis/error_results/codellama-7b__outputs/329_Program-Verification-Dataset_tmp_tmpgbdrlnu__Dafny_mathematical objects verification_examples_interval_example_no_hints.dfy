
function foo(x: int)
  requires x >= 0
  ensures x == 0
{
  if x > 0 {
    UpdateStmt(x - 1);
  }
  return x;
}

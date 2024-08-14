
function xtr<T>(xs: list<T>, ys: list<T>): list<T>
  requires xs != nil && ys != nil
{
  if xs == nil then ys
  else if ys == nil then xs
  else Cons(head(xs), xtr(tail(xs), ys))
}

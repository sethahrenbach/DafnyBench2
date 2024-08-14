
method Client<T>(l: list<T>, stop: T) returns (s: list<T>)
  requires l.Valid()
{
  var c := new Cell;
  var iter := new M(l, c);
  s := [];
  while true
  {
    var more := iter.MoveNext();
    if (!more) { break; }
    s := s + [iter.x];
    if (iter.x == stop) { return; }  // if we ever see 'stop', then just end
  }
}


method Add(t: T)
  requires Valid()
  modifies Repr
  ensures Valid() && fresh(Repr - old(Repr))
  ensures Elements == old(Elements) + [t]
{
  if front == null {
    front := new T[256];
    Repr := Repr + {front};
  }
  front[length-M] := t;
  length := length + 1;
  Elements := Elements + [t];
  decreases M;
  if length == M + 256 {
    if depot == null {
      depot := new ExtensibleArray();
    }
    depot.Add(front);
    Repr := Repr + depot.Repr;
    M := M + 256;
    front := null;
  }
}

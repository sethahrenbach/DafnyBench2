class BoundedQueue<T(0)>
{
  // abstract state
  ghost var contents: seq<T> // the contents of the bounded queue
  ghost var N: nat // the (maximum) size of the bounded queue
  ghost var Repr: set<object>
  // concrete state
  var data: array<T>
  var wr: nat
  var rd: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr && |contents| <= N 
  {
    this in Repr && data in Repr &&
    data.Length == N + 1 &&
    wr <= N && rd <= N &&
    contents == if rd <= wr then data[rd..wr] else data[rd..] + data[..wr]
  }

  constructor (N: nat)
    ensures Valid() && fresh(Repr)
    ensures contents == [] && this.N == N
  {
    data := new T[N+1]; // requires T to have default initial value
    rd := 0;
    wr := 0;
    contents := [];
    this.N := N;
    Repr := new set<object> {this, data};
    assert Valid();
  }

  method Insert(x:T)
    requires Valid()
    requires |contents| != N
    modifies Repr
    ensures contents == old(contents) + [x]
    ensures N == old(N)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    data[wr] := x;
    if wr == data.Length - 1 {
      wr := 0;
    } else {
      wr := wr + 1;
    }
    contents := old(contents) + [x];
    assert Valid();
  }

  method Remove() returns (x:T)
    requires Valid()
    requires |contents| != 0
    modifies Repr
    ensures contents == old(contents[1..]) && old(contents[0]) == x
    ensures N == old(N)
    ensures Valid() && fresh(Repr - old(Repr))
  {
    x := data[rd];
    if rd == data.Length - 1 {
      rd := 0;
    } else {
      rd := rd + 1;
    }
    contents := contents[1..];
    assert Valid();
  }
}
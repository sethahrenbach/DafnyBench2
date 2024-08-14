
datatype Tree<V> = Leaf(V) | SingleNode(V, Tree<V>) | DoubleNode(V, Tree<V>, Tree<V>)

datatype Code<V> = CLf(V) | CSNd(V) | CDNd(V)

function serialise<V>(t : Tree<V>) : seq<Code<V>> 
{
  match t {
    case Leaf(v) => [ CLf(v) ]
    case SingleNode(v, t) => serialise(t) + [ CSNd(v) ]
    case DoubleNode(v, t1, t2) => serialise(t2) + serialise(t1) + [ CDNd(v) ]
  }
}

function deserialiseAux<T>(codes: seq<Code<T>>, trees: seq<Tree<T>>): seq<Tree<T>>
  requires |codes| > 0 || |trees| > 0
  ensures |deserialiseAux(codes, trees)| >= 0
{
  if |codes| == 0 then trees
  else
    match codes[0] {
      case CLf(v) => deserialiseAux(codes[1..], trees + [Leaf(v)])
      case CSNd(v) => if (|trees| >= 1) then deserialiseAux(codes[1..], trees[..|trees|-1] + [SingleNode(v, trees[|trees|-1])]) else trees
      case CDNd(v) => if (|trees| >= 2) then deserialiseAux(codes[1..], trees[..|trees|-2] + [DoubleNode(v, trees[|trees|-1], trees[|trees|-2])]) else trees
    }
}

function deserialise<T>(s:seq<Code<T>>):seq<Tree<T>>
  requires |s| > 0
{
  deserialiseAux(s, [])
}

lemma SerialiseDeserialiseLemma<V>(t: Tree<V>)
  ensures deserialise(serialise(t)) == [t]
{
  var s := serialise(t);
  var d := deserialise(s);
  assert d == [t];
}

lemma DeserialiseAfterSerialiseLemma<T>(t: Tree<T>, cds: seq<Code<T>>, ts: seq<Tree<T>>)
  ensures deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + [t])
{
  match t {
    case Leaf(x) =>
      assert deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + [t]);
    case SingleNode(x, t1) =>
      DeserialiseAfterSerialiseLemma(t1, [CSNd(x)] + cds, ts);
      assert deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + [t]);
    case DoubleNode(x, t1, t2) =>
      DeserialiseAfterSerialiseLemma(t2, serialise(t1) + [CDNd(x)] + cds, ts);
      DeserialiseAfterSerialiseLemma(t1, [CDNd(x)] + cds, ts + [t2]);
      assert deserialiseAux(serialise(t) + cds, ts) == deserialiseAux(cds, ts + [t]);
  }
}

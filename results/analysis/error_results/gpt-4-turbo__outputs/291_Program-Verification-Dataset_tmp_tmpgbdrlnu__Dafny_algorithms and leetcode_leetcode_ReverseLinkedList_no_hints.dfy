
datatype ListNode = Null | Node(val: nat, next: ListNode)

function reverseList(xs: ListNode): ListNode
  decreases xs // Ensures termination by structural recursion
{
  if xs == Null then
    Null
  else
    nodeConcat(reverseList(xs.next), Node(xs.val, Null))
}

function nodeConcat(xs: ListNode, end: ListNode): ListNode
  decreases xs // Ensures termination by structural recursion
{
  if xs == Null then
    end
  else
    Node(xs.val, nodeConcat(xs.next, end))
}

lemma ConcatNullIsRightIdentity(xs: ListNode)
  ensures nodeConcat(xs, Null) == xs
  decreases xs // Ensures termination by structural recursion
{
  if xs != Null {
    ConcatNullIsRightIdentity(xs.next);
  }
}

lemma ConcatNullIsLeftIdentity(xs: ListNode)
  ensures nodeConcat(Null, xs) == xs
{
}

lemma ConcatExtensionality(xs: ListNode)
  requires xs != Null
  ensures nodeConcat(Node(xs.val, Null), xs.next) == xs
  decreases xs // Ensures termination by structural recursion
{
  if xs.next != Null {
    ConcatExtensionality(xs.next);
  }
}

lemma ConcatAssociative(xs: ListNode, ys: ListNode, zs: ListNode)
  ensures nodeConcat(nodeConcat(xs, ys), zs) == nodeConcat(xs, nodeConcat(ys, zs))
  decreases xs // Ensures termination by structural recursion
{
  if xs != Null {
    ConcatAssociative(xs.next, ys, zs);
  }
}

lemma ConcatReverseList(xs: ListNode, ys: ListNode)
  ensures reverseList(nodeConcat(xs, ys)) == nodeConcat(reverseList(ys), reverseList(xs))
  decreases xs // Ensures termination by structural recursion
{
  if xs == Null {
    assert reverseList(nodeConcat(xs, ys)) == reverseList(ys);
    assert nodeConcat(reverseList(ys), reverseList(xs)) == reverseList(ys);
  } else {
    ConcatReverseList(xs.next, ys);
    assert reverseList(nodeConcat(xs, ys)) == nodeConcat(reverseList(ys), reverseList(xs));
  }
}

lemma reverseReverseListIsIdempotent(xs: ListNode)
  ensures reverseList(reverseList(xs)) == xs
  decreases xs // Ensures termination by structural recursion
{
  if xs == Null {
  } else {
    reverseReverseListIsIdempotent(xs.next);
    assert reverseList(reverseList(xs)) == xs;
  }
}

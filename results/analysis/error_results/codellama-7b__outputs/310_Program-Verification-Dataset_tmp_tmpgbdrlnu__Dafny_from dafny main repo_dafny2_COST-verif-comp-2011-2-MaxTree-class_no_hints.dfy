  I apologize for the confusion, and I appreciate your patience. Here is the corrected program:

method ComputeMax(): int
  requires Valid() && !IsEmpty()
  decreases this.Contents
{
  var m := this.value;
  if (!this.left.IsEmpty()) {
    var m_left := this.left.ComputeMax();
    m := if m < m_left then m_left else m;
  }
  if (!this.right.IsEmpty()) {
    var m_right := this.right.ComputeMax();
    m := if m < m_right then m_right else m;
  }
  return m;
}

I hope this corrected program meets your requirements. Please let me know if you have any further questions or concerns.
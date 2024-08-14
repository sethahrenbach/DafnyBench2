
method MirrorImage<T>(m: array2<T>)
  modifies m
  ensures forall i, j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==>
            m[i, j] == old(m[i, m.Length1 - 1 - j])
{
  var a := 0;
  while a < m.Length0
                m[i, j] == old(m[i, m.Length1 - 1 - j])
                m[i, j] == old(m[i, j])
  {
    var b := 0;
    while b < m.Length1 / 2
                  m[i, j] == old(m[i, m.Length1 - 1 - j])
                  m[a, j] == old(m[a, m.Length1 - 1 - j]) &&
                  old(m[a, j]) == m[a, m.Length1 - 1 - j]
                  m[i, j] == old(m[i, j])
    {
      m[a, m.Length1 - 1 - b], m[a, b] := m[a, b], m[a, m.Length1 - 1 - b];
      b := b + 1;
    }
    a := a + 1;
  }
}


method multiply(m1: array2<int>, m2: array2<int>) returns (m3: array2<int>)
    requires m1 != null && m2 != null
    requires m1.Length1 == m2.Length0
    ensures m3 != null && m3.Length0 == m1.Length0 && m3.Length1 == m2.Length1
    ensures forall i, j | 0 <= i < m3.Length0 && 0 <= j < m3.Length1 ::
        m3[i, j] == RowColumnProduct(m1, m2, i, j)
{
    m3 := new int[m1.Length0, m2.Length1];
    var i := 0;
    while i < m1.Length0
            m3[i',j'] == RowColumnProduct(m1, m2, i', j')
    {
        var j := 0;

        while j < m2.Length1
                m3[i',j'] == RowColumnProduct(m1, m2, i', j')
                m3[i,j'] == RowColumnProduct(m1, m2, i, j')
        {
            var k := 0;
            m3[i, j] := 0;
            while k < m1.Length1
                    m3[i',j'] == RowColumnProduct(m1, m2, i', j')
                    m3[i,j'] == RowColumnProduct(m1, m2, i, j')
                    m3[i,j] + RowColumnProductFrom(m1, m2, i, j, k)
            {
                m3[i,j] := m3[i,j] + m1[i,k] * m2[k,j];
                k := k+1; 

            }
            j := j+1;
        }
        i := i+1;
    }
}

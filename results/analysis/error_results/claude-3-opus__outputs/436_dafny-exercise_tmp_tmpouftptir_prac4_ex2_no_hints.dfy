predicate triple(a: array<int>) 
reads a
{
	exists i :: 0 <= i < a.Length - 2 && a[i] == a[i + 1] == a[i + 2]
}

method GetTriple(a: array<int>) returns (index: int)
ensures 0 <= index < a.Length - 2 || index == a.Length
ensures index == a.Length <==> !triple(a)
ensures 0 <= index < a.Length - 2 <==> triple(a)
ensures 0 <= index < a.Length - 2 ==> a[index] == a[index + 1] == a[index + 2]
{
	var i: nat := 0;
	index := a.Length;
	if a.Length < 3 {
		return;
	}
	while i < a.Length - 2
	invariant 0 <= i <= a.Length - 2
	invariant forall j :: 0 <= j < i ==> a[j] != a[j + 1] || a[j + 1] != a[j + 2]
	invariant index == a.Length || (0 <= index < a.Length - 2 && a[index] == a[index + 1] == a[index + 2])
	{
		if a[i] == a[i + 1] == a[i + 2] {
			index := i;
			return;
		}
		i := i + 1;
	}
}

method TesterGetTriple()
{
    var a: array<int> := new int[1][42];
    var b := GetTriple(a);
    assert b == 1;

    a := new int[2][42,42];
    b := GetTriple(a);
    assert b == 2;

    a := new int[3][42,42,0];
    b := GetTriple(a);
    assert b == 3;

    a := new int[4][42,42,0,42];
    b := GetTriple(a);
    assert b == 4;

    a := new int[3][42,42,42];
    b := GetTriple(a);
    assert b == 0;

    a := new int[4][0,42,42,42];
    b := GetTriple(a);
    assert b == 1;

    a := new int[6][0,0,42,42,42,0];
    b := GetTriple(a);
    assert b == 2;
}
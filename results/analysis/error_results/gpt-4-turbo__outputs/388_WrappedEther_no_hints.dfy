module Int {
    const TWO_7   : int := 0x0_80;
    const TWO_8   : int := 0x1_00;
    const TWO_15  : int := 0x0_8000;
    const TWO_16  : int := 0x1_0000;
    const TWO_24  : int := 0x1_0000_00;
    const TWO_31  : int := 0x0_8000_0000;
    const TWO_32  : int := 0x1_0000_0000;
    const TWO_40  : int := 0x1_0000_0000_00;
    const TWO_48  : int := 0x1_0000_0000_0000;
    const TWO_56  : int := 0x1_0000_0000_0000_00;
    const TWO_63  : int := 0x0_8000_0000_0000_0000;
    const TWO_64  : int := 0x1_0000_0000_0000_0000;
    const TWO_127 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000;
    const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000;
    const TWO_160 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
    const TWO_255 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
    const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;

    const MIN_I8   : int := -TWO_7;
    const MAX_I8   : int :=  TWO_7 - 1;
    const MIN_I16  : int := -TWO_15;
    const MAX_I16  : int :=  TWO_15 - 1;
    const MIN_I32  : int := -TWO_31;
    const MAX_I32  : int :=  TWO_31 - 1;
    const MIN_I64  : int := -TWO_63;
    const MAX_I64  : int :=  TWO_63 - 1;
    const MIN_I128 : int := -TWO_127;
    const MAX_I128 : int :=  TWO_127 - 1;
    const MIN_I256 : int := -TWO_255;
    const MAX_I256 : int :=  TWO_255 - 1;

    const MAX_U8 : int :=  TWO_8 - 1;
    const MAX_U16 : int := TWO_16 - 1;
    const MAX_U24 : int := TWO_24 - 1;
    const MAX_U32 : int := TWO_32 - 1;
    const MAX_U40 : int := TWO_40 - 1;
    const MAX_U48 : int := TWO_48 - 1;
    const MAX_U56 : int := TWO_56 - 1;
    const MAX_U64 : int := TWO_64 - 1;
    const MAX_U128 : int := TWO_128 - 1;
    const MAX_U160: int := TWO_160 - 1;
    const MAX_U256: int := TWO_256 - 1;

    function Max(i1: int, i2: int): int {
        if i1 >= i2 then i1 else i2
    }

    function Min(i1: int, i2: int): int {
        if i1 < i2 then i1 else i2
    }

    function RoundUp(i: int, r: nat): int
        requires r > 0
        ensures (i % r) == 0 ==> RoundUp(i, r) == i
        ensures (i % r) != 0 ==> RoundUp(i, r) == ((i / r) * r + r)
    {
        if (i % r) == 0 then i
        else ((i / r) * r) + r
    }

    function MaxUnsignedN(n: nat): nat
        requires 1 <= n <= 32
        ensures MaxUnsignedN(n) == (Pow(2, n * 8) - 1)
    {
        match n {
            case 1 => MAX_U8,
            case 2 => MAX_U16,
            case 3 => MAX_U24,
            case 4 => MAX_U32,
            case 5 => MAX_U40,
            case 6 => MAX_U48,
            case 7 => MAX_U56,
            case 8 => MAX_U64,
            case 16 => MAX_U128,
            case 20 => MAX_U160,
            case 32 => MAX_U256,
            case _ => Pow(2, n * 8) - 1
        }
    }

    function Pow(n: nat, k: nat): nat
        ensures n > 0 ==> Pow(n, k) > 0
    {
        if k == 0 then 1
        else if k == 1 then n
        else {
            var p := k / 2;
            var np := Pow(n, p);
            if p * 2 == k then np * np
            else np * np * n
        }
    }
}
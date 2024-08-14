/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
module Int {
    const TWO_7   : int := 0x0_80
    const TWO_8   : int := 0x1_00
    const TWO_15  : int := 0x0_8000
    const TWO_16  : int := 0x1_0000
    const TWO_24  : int := 0x1_0000_00
    const TWO_31  : int := 0x0_8000_0000
    const TWO_32  : int := 0x1_0000_0000
    const TWO_40  : int := 0x1_0000_0000_00
    const TWO_48  : int := 0x1_0000_0000_0000
    const TWO_56  : int := 0x1_0000_0000_0000_00
    const TWO_63  : int := 0x0_8000_0000_0000_0000
    const TWO_64  : int := 0x1_0000_0000_0000_0000
    const TWO_127 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000
    const TWO_128 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_160 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_255 : int := 0x0_8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000
    const TWO_256 : int := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

    // Signed Integers
    const MIN_I8   : int := -TWO_7
    const MAX_I8   : int :=  TWO_7 - 1
    const MIN_I16  : int := -TWO_15
    const MAX_I16  : int :=  TWO_15 - 1
    const MIN_I32  : int := -TWO_31
    const MAX_I32  : int :=  TWO_31 - 1
    const MIN_I64  : int := -TWO_63
    const MAX_I64  : int :=  TWO_63 - 1
    const MIN_I128 : int := -TWO_127
    const MAX_I128 : int :=  TWO_127 - 1
    const MIN_I256 : int := -TWO_255
    const MAX_I256 : int :=  TWO_255 - 1

    newtype{:nativeType "sbyte"} i8 = i:int   | MIN_I8 <= i <= MAX_I8
    newtype{:nativeType "short"} i16 = i:int  | MIN_I16 <= i <= MAX_I16
    newtype{:nativeType "int"}   i32 = i:int  | MIN_I32 <= i <= MAX_I32
    newtype{:nativeType "long"}  i64 = i:int  | MIN_I64 <= i <= MAX_I64
    newtype i128 = i:int | MIN_I128 <= i <= MAX_I128
    newtype i256 = i:int | MIN_I256 <= i <= MAX_I256

    // Unsigned Integers
    const MAX_U8 : int :=  TWO_8 - 1
    const MAX_U16 : int := TWO_16 - 1
    const MAX_U24 : int := TWO_24 - 1
    const MAX_U32 : int := TWO_32 - 1
    const MAX_U40 : int := TWO_40 - 1
    const MAX_U48 : int := TWO_48 - 1
    const MAX_U56 : int := TWO_56 - 1
    const MAX_U64 : int := TWO_64 - 1
    const MAX_U128 : int := TWO_128 - 1
    const MAX_U160: int := TWO_160 - 1
    const MAX_U256: int := TWO_256 - 1

    newtype{:nativeType "byte"} u8 = i:int    | 0 <= i <= MAX_U8
    newtype{:nativeType "ushort"} u16 = i:int | 0 <= i <= MAX_U16
    newtype{:nativeType "uint"} u24 = i:int | 0 <= i <= MAX_U24
    newtype{:nativeType "uint"} u32 = i:int   | 0 <= i <= MAX_U32
    newtype{:nativeType "ulong"} u40 = i:int   | 0 <= i <= MAX_U40
    newtype{:nativeType "ulong"} u48 = i:int   | 0 <= i <= MAX_U48
    newtype{:nativeType "ulong"} u56 = i:int   | 0 <= i <= MAX_U56
    newtype{:nativeType "ulong"} u64 = i:int  | 0 <= i <= MAX_U64
    newtype u128 = i:int | 0 <= i <= MAX_U128
    newtype u160 = i:int | 0 <= i <= MAX_U160
    newtype u256 = i:int | 0 <= i <= MAX_U256


    // Determine maximum of two u256 integers.
    function Max(i1: int, i2: int) : int {
        if i1 >= i2 then i1 else i2
    }

    // Determine maximum of two u256 integers.
    function Min(i1: int, i2: int) : int {
        if i1 < i2 then i1 else i2
    }

    // Round up a given number (i) by a given multiple (r).
    function RoundUp(i: int, r: nat) : int
    requires r > 0 {
        if (i % r) == 0 then i
        else
        ((i/r)*r) + r
    }

    // Return the maximum value representable using exactly n unsigned bytes.
    // This is essentially computing (2^n - 1).  However, the point of doing it
    // in this fashion is to avoid using Pow() as this is challenging for the
    // verifier.
    function MaxUnsignedN(n:nat) : (r:nat)
    requires 1 <= n <= 32 {
        match n
            case 1 => MAX_U8
            case 2 => MAX_U16
            case 3 => MAX_U24
            case 4 => MAX_U32
            case 5 => MAX_U40
            case 6 => MAX_U48
            case 7 => MAX_U56
            case 8 => MAX_U64
            case 16 => MAX_U128
            case 20 => MAX_U160
            case 32 => MAX_U256
            // Fall back case (for now)
            case _ =>
                Pow(2,n) - 1
    }


    // =========================================================
    // Exponent
    // =========================================================

    /**
     * Compute n^k.
     */
    function Pow(n:nat, k:nat) : (r:nat)
    // Following needed for some proofs
    ensures n > 0 ==> r > 0 {
        if k == 0 then 1
        else if k == 1 then n
        else
            var p := k / 2;
            var np := Pow(n,p);
            if p*2 == k then np * np
            else np * np * n
    }

    // Simple lemma about POW.
    lemma lemma_pow2(k:nat)
    ensures Pow(2,k) > 0 {
        if k == 0 {
        } else if k == 1 {
            } else {
            lemma_pow2(k/2);
        }
    }

    // =========================================================
    // Non-Euclidean Division / Remainder
    // =========================================================

    // This provides a non-Euclidean division operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  This operator, therefore,
    // always divides *towards* zero.
    function Div(lhs: int, rhs: int) : int
    requires rhs != 0 {
        if lhs >= 0 then lhs / rhs
        else
        -((-lhs) / rhs)
    }

    // This provides a non-Euclidean Remainder operator and is necessary
    // because Dafny (unlike just about every other programming
    // language) supports Euclidean division.  Observe that this is a
    // true Remainder operator, and not a modulus operator.  For
    // emxaple, this means the result can be negative.
    function Rem(lhs: int, rhs: int) : int
    requires rhs != 0 {
        if lhs >= 0 then (lhs % rhs)
        else
        var d := -((-lhs) / rhs);
        lhs - (d * rhs)
    }
}

/**
 * Various helper methods related to unsigned 8bit integers.
 */
module U8 {
    import opened Int
    // Compute the log of a value at base 2 where the result is rounded down.
    function Log2(v:u8) : (r:nat)
    ensures r < 8 {
        // Split 4 bits
        if v <= 15 then
            // Split 2 bits
            if v <= 3 then
                // Split 1 bit
                if v <= 1 then 0 else 1
            else
                // Split 1 bit
                if v <= 7 then 2 else 3
        else
            // Split 2 bits
            if v <= 63 then
                // Split 1 bit
                if v <= 31 then 4 else 5
            else
                // Split 1 bit
                if v <= 127 then 6 else 7
    }
}

/**
 * Various helper methods related to unsigned 16bit integers.
 */
module U16 {
    import opened Int
    import U8

    // Read nth 8bit word (i.e. byte) out of this u16, where 0
    // identifies the most significant byte.
    function NthUint8(v:u16, k: nat) : u8
        // Cannot read more than two words!
    requires k < 2 {
        if k == 0
            then (v / (TWO_8 as u16)) as u8
        else
            (v % (TWO_8 as u16)) as u8
    }

    /**
     * Compute the log of a value at base 2 where the result is rounded down.
     */
    function Log2(v:u16) : (r:nat)
    ensures r < 16 {
        var low := (v % (TWO_8 as u16)) as u8;
        var high := (v / (TWO_8 as u16)) as u8;
        if high != 0 then U8.Log2(high)+8 else U8.Log2(low)
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u16) : (r:nat)
    ensures r <= 1 {
        var low := (v % (TWO_8 as u16)) as u8;
        var high := (v / (TWO_8 as u16)) as u8;
        if high != 0 then 1 else 0
    }

    /**
     * Convert a u16 into a sequence of 2 bytes (in big endian representation).
     */
    function ToBytes(v:u16) : (r:seq<u8>)
    ensures |r| == 2 {
        var low := (v % (TWO_8 as u16)) as u8;
        var high := (v / (TWO_8 as u16)) as u8;
        [high,low]
    }

    function Read(bytes: seq<u8>, address:nat) : u16
    requires (address+1) < |bytes| {
        var b1 := bytes[address] as u16;
        var b2 := bytes[address+1] as u16;
        (b1 * (TWO_8 as u16)) + b2
    }
}

/**
 * Various helper methods related to unsigned 32bit integers.
 */
module U32 {
    import U16
    import opened Int

    // Read nth 16bit word out of this u32, where 0 identifies the most
    // significant word.
    function NthUint16(v:u32, k: nat) : u16
        // Cannot read more than two words!
    requires k < 2 {
        if k == 0
            then (v / (TWO_16 as u32)) as u16
        else
            (v % (TWO_16 as u32)) as u16
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log2(v:u32) : (r:nat)
    ensures r < 32 {
        var low := (v % (TWO_16 as u32)) as u16;
        var high := (v / (TWO_16 as u32)) as u16;
        if high != 0 then U16.Log2(high)+16 else U16.Log2(low)
    }

    /**
     * Compute the log of a value at base 256 where the result is rounded down.
     */
    function Log256(v:u32) : (r:nat)
    ensures r <= 3 {
        var low := (v % (TWO_16 as u32)) as u16;
        var high := (v / (TWO_16 as u32)) as u16;
        if high != 0 then U16.Log256(high)+2 else U16.Log256(low)
    }

    /**
     * Convert a u32 into a sequence of 4 bytes (in big endian representation).
     */
    function ToBytes(v:u32) : (r:seq<u8>)
    ensures |r| == 4 {
        var low := (v % (TWO_16 as u32)) as u16;
        var high := (v / (TWO_16 as u32)) as u16;
        U16.ToBytes(high) + U16.ToBytes(low)
    }

    function Read(bytes: seq<u8>, address:nat) : u32
    requires (address+3) < |bytes| {
        var b1 := U16.Read(bytes, address) as u32;
        var b2 := U16.Read(bytes, address+2) as u32;
        (b1 * (TWO_16 as u32)) + b2
    }
}

/**
 * Various helper methods related to unsigned 64bit integers.
 

method GenerateRandomString(length: int) returns (str: string)
    ensures str.Length == length
{
    var result: string := "";
    for (var i: int := 0; i < length; i++)
    {
        result += (char)('a' + (int)(Math.Random() * 26));
    }
    return result;
}

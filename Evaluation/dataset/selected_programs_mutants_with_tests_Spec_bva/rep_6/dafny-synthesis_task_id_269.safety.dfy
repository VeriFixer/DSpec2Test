method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test9() {
var r0 := AsciiValue('\U{0001}');
expect r0 == '\U{0001}' as int;
}

// REPEAT 6 - TIME: 8.3642895 s

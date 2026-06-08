method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test8() {
var r0 := AsciiValue('\U{0003}');
expect r0 == '\U{0003}' as int;
}

// REPEAT 5 - TIME: 8.4338105 s

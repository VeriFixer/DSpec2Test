method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test7() {
var r0 := AsciiValue('\U{0004}');
expect r0 == '\U{0004}' as int;
}

// REPEAT 4 - TIME: 6.9511355 s

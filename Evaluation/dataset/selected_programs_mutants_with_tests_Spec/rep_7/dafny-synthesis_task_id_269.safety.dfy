method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test6() {
var r0 := AsciiValue('\0');
expect r0 == '\0' as int;
}

// REPEAT 7 - TIME: 7.8622227 s

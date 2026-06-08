method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test7() {
var r0 := AsciiValue('\'');
expect r0 == '\'' as int;
}

// REPEAT 8 - TIME: 7.9083438 s

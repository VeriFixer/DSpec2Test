method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test11() {
var r0 := AsciiValue('\'');
expect r0 == '\'' as int;
}

// REPEAT 8 - TIME: 10.8273318 s

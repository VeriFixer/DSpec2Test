method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test12() {
var r0 := AsciiValue('\U{22BE}');
expect r0 == '\U{22BE}' as int;
}

// REPEAT 9 - TIME: 10.5342889 s

method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test9() {
var r0 := AsciiValue('\U{22BD}');
expect r0 == '\U{22BD}' as int;
}

// REPEAT 10 - TIME: 9.7545071 s

method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test1() {
var r0 := AsciiValue('%');
expect r0 == '%' as int;
}

// REPEAT 2 - TIME: 3.1897575 s

method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test0() {
var r0 := AsciiValue('&');
expect r0 == '&' as int;
}
method {:test} Test2() {
var r0 := AsciiValue('d');
expect r0 == 'd' as int;
}

// REPEAT 1 - TIME: 4.7223029 s

method {:test} Test5() {
var r0 := AsciiValue('%');
expect r0 == '%' as int;
}

// REPEAT 2 - TIME: 5.4581117 s

method {:test} Test6() {
var r0 := AsciiValue('\U{0005}');
expect r0 == '\U{0005}' as int;
}

// REPEAT 3 - TIME: 6.2552193 s

method {:test} Test7() {
var r0 := AsciiValue('\U{0004}');
expect r0 == '\U{0004}' as int;
}

// REPEAT 4 - TIME: 6.9511355 s

method {:test} Test8() {
var r0 := AsciiValue('\U{0003}');
expect r0 == '\U{0003}' as int;
}

// REPEAT 5 - TIME: 7.6667336 s

method {:test} Test9() {
var r0 := AsciiValue('\U{0001}');
expect r0 == '\U{0001}' as int;
}

// REPEAT 6 - TIME: 8.3642895 s

method {:test} Test10() {
var r0 := AsciiValue('\0');
expect r0 == '\0' as int;
}

// REPEAT 7 - TIME: 9.0689462 s

method {:test} Test11() {
var r0 := AsciiValue('\'');
expect r0 == '\'' as int;
}

// REPEAT 8 - TIME: 9.8457375 s

method {:test} Test12() {
var r0 := AsciiValue('\U{22BE}');
expect r0 == '\U{22BE}' as int;
}

// REPEAT 9 - TIME: 10.5342889 s

method {:test} Test13() {
var r0 := AsciiValue('\U{22BD}');
expect r0 == '\U{22BD}' as int;
}

// REPEAT 10 - TIME: 11.2631657 s

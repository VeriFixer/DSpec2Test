method {:testEntry} AsciiValue(c: char) returns (ascii: int)
    ensures ascii == c as int
{
    ascii := c as int;
}

method {:test} Test0() {
var r0 := AsciiValue('&');
expect r0 == '&' as int;
}

// REPEAT 1 - TIME: 2.319738 s

method {:test} Test1() {
var r0 := AsciiValue('%');
expect r0 == '%' as int;
}

// REPEAT 2 - TIME: 3.2787993 s

method {:test} Test2() {
var r0 := AsciiValue('\U{0005}');
expect r0 == '\U{0005}' as int;
}

// REPEAT 3 - TIME: 4.1303295 s

method {:test} Test3() {
var r0 := AsciiValue('\U{0004}');
expect r0 == '\U{0004}' as int;
}

// REPEAT 4 - TIME: 5.0339586 s

method {:test} Test4() {
var r0 := AsciiValue('\U{0003}');
expect r0 == '\U{0003}' as int;
}

// REPEAT 5 - TIME: 6.0311602 s

method {:test} Test5() {
var r0 := AsciiValue('\U{0001}');
expect r0 == '\U{0001}' as int;
}

// REPEAT 6 - TIME: 6.8430293 s

method {:test} Test6() {
var r0 := AsciiValue('\0');
expect r0 == '\0' as int;
}

// REPEAT 7 - TIME: 7.5397013 s

method {:test} Test7() {
var r0 := AsciiValue('\'');
expect r0 == '\'' as int;
}

// REPEAT 8 - TIME: 8.145282 s

method {:test} Test8() {
var r0 := AsciiValue('\U{22BE}');
expect r0 == '\U{22BE}' as int;
}

// REPEAT 9 - TIME: 9.048219 s

method {:test} Test9() {
var r0 := AsciiValue('\U{22BD}');
expect r0 == '\U{22BD}' as int;
}

// REPEAT 10 - TIME: 9.7545071 s

method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test0() {
var r0 := CountCharacters("a");
expect r0 >= 0;
expect r0 == |"a"|;
}
method {:test} Test1() {
var r0 := CountCharacters("");
expect r0 >= 0;
expect r0 == |""|;
}
method {:test} Test3() {
var r0 := CountCharacters("aa");
expect r0 >= 0;
expect r0 == |"aa"|;
}

// REPEAT 1 - TIME: 6.0027697 s

method {:test} Test8() {
var r0 := CountCharacters("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 2 - TIME: 7.3307645 s

method {:test} Test9() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 3 - TIME: 8.2516271 s

method {:test} Test10() {
var r0 := CountCharacters("\U{0004}\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0\U{0002}"|;
}

// REPEAT 4 - TIME: 9.1663772 s

method {:test} Test11() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 5 - TIME: 9.8213424 s

method {:test} Test12() {
var r0 := CountCharacters("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"|;
}

// REPEAT 6 - TIME: 10.7487183 s

method {:test} Test13() {
var r0 := CountCharacters("\U{0006}\0\U{0004}\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0006}\0\U{0004}\U{0002}"|;
}

// REPEAT 7 - TIME: 11.4985994 s

method {:test} Test14() {
var r0 := CountCharacters("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"|;
}

// REPEAT 8 - TIME: 12.3325135 s

method {:test} Test15() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 9 - TIME: 13.1660483 s

method {:test} Test16() {
var r0 := CountCharacters("\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\0\U{0002}"|;
}

// REPEAT 10 - TIME: 14.0193318 s

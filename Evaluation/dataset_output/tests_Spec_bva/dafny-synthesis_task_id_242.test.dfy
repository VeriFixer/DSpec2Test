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

// REPEAT 1 - TIME: 6.4736066 s

method {:test} Test8() {
var r0 := CountCharacters("a\0aaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaa\U{0002}"|;
}

// REPEAT 2 - TIME: 7.231484 s

method {:test} Test9() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 3 - TIME: 7.834041 s

method {:test} Test10() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 4 - TIME: 8.5062048 s

method {:test} Test11() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 5 - TIME: 9.1498319 s

method {:test} Test12() {
var r0 := CountCharacters("\U{0002}\0aaa\U{0004}aaaaaaa\U{0006}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaa\U{0004}aaaaaaa\U{0006}"|;
}

// REPEAT 6 - TIME: 9.8067337 s

method {:test} Test13() {
var r0 := CountCharacters("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"|;
}

// REPEAT 7 - TIME: 10.3384995 s

method {:test} Test14() {
var r0 := CountCharacters("\0aaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 8 - TIME: 10.9474167 s

method {:test} Test15() {
var r0 := CountCharacters("\U{0004}\0\U{0002}\U{0006}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0\U{0002}\U{0006}"|;
}

// REPEAT 9 - TIME: 11.489536 s

method {:test} Test16() {
var r0 := CountCharacters("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"|;
}

// REPEAT 10 - TIME: 12.2922758 s

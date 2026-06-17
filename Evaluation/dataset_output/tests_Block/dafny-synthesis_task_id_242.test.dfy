method {:testEntry} CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
{
    count := |s|;
}

method {:test} Test0() {
var r0 := CountCharacters("");
expect r0 >= 0;
expect r0 == |""|;
}

// REPEAT 1 - TIME: 1.9183343 s

method {:test} Test1() {
var r0 := CountCharacters("a");
expect r0 >= 0;
expect r0 == |"a"|;
}

// REPEAT 2 - TIME: 2.6121907 s

method {:test} Test2() {
var r0 := CountCharacters("aa");
expect r0 >= 0;
expect r0 == |"aa"|;
}

// REPEAT 3 - TIME: 3.2364811 s

method {:test} Test3() {
var r0 := CountCharacters("a\0a");
expect r0 >= 0;
expect r0 == |"a\0a"|;
}

// REPEAT 4 - TIME: 3.8611712 s

method {:test} Test4() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 5 - TIME: 4.505348 s

method {:test} Test5() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 6 - TIME: 5.1429836 s

method {:test} Test6() {
var r0 := CountCharacters("\U{0002}\0aaaaaaaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaaaaaaaaaaa\U{0004}"|;
}

// REPEAT 7 - TIME: 5.8482553 s

method {:test} Test7() {
var r0 := CountCharacters("a\0aaaaa\U{0002}aaaaaaa\U{0004}");
expect r0 >= 0;
expect r0 == |"a\0aaaaa\U{0002}aaaaaaa\U{0004}"|;
}

// REPEAT 8 - TIME: 6.5112136 s

method {:test} Test8() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 9 - TIME: 7.1948219 s

method {:test} Test9() {
var r0 := CountCharacters("\U{0004}\0a\U{0002}aaaaaaa\U{0006}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0a\U{0002}aaaaaaa\U{0006}"|;
}

// REPEAT 10 - TIME: 8.0190551 s

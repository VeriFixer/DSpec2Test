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

// REPEAT 1 - TIME: 2.3963452 s

method {:test} Test1() {
var r0 := CountCharacters("a\0");
expect r0 >= 0;
expect r0 == |"a\0"|;
}

// REPEAT 2 - TIME: 3.2354209 s

method {:test} Test2() {
var r0 := CountCharacters("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 3 - TIME: 4.1084325 s

method {:test} Test3() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 4 - TIME: 4.9885919 s

method {:test} Test4() {
var r0 := CountCharacters("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 5 - TIME: 5.7581589 s

method {:test} Test5() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 6 - TIME: 6.450481 s

method {:test} Test6() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 7 - TIME: 7.16293 s

method {:test} Test7() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 8 - TIME: 7.8051941 s

method {:test} Test8() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 9 - TIME: 8.3663277 s

method {:test} Test9() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 10 - TIME: 9.021176 s

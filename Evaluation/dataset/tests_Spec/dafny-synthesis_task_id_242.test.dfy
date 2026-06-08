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

// REPEAT 1 - TIME: 2.7990675 s

method {:test} Test1() {
var r0 := CountCharacters("a\0");
expect r0 >= 0;
expect r0 == |"a\0"|;
}

// REPEAT 2 - TIME: 3.742235 s

method {:test} Test2() {
var r0 := CountCharacters("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 3 - TIME: 4.6069909 s

method {:test} Test3() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 4 - TIME: 5.6067946 s

method {:test} Test4() {
var r0 := CountCharacters("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 5 - TIME: 6.7610987 s

method {:test} Test5() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 6 - TIME: 7.6693342 s

method {:test} Test6() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 7 - TIME: 8.6148644 s

method {:test} Test7() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 8 - TIME: 9.6437032 s

method {:test} Test8() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 9 - TIME: 10.5128696 s

method {:test} Test9() {
var r0 := CountCharacters("\0a");
expect r0 >= 0;
expect r0 == |"\0a"|;
}

// REPEAT 10 - TIME: 11.5228576 s

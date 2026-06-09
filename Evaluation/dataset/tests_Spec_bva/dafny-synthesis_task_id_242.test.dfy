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

// REPEAT 1 - TIME: 6.0197212 s

method {:test} Test8() {
var r0 := CountCharacters("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
expect r0 == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
}

// REPEAT 2 - TIME: 6.9151572 s

method {:test} Test9() {
var r0 := CountCharacters("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"|;
}

// REPEAT 3 - TIME: 7.6586897 s

method {:test} Test10() {
var r0 := CountCharacters("\U{0004}\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0004}\0\U{0002}"|;
}

// REPEAT 4 - TIME: 8.4651371 s

method {:test} Test11() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 5 - TIME: 9.1608103 s

method {:test} Test12() {
var r0 := CountCharacters("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"|;
}

// REPEAT 6 - TIME: 9.9322968 s

method {:test} Test13() {
var r0 := CountCharacters("\U{0006}\0\U{0004}\U{0002}");
expect r0 >= 0;
expect r0 == |"\U{0006}\0\U{0004}\U{0002}"|;
}

// REPEAT 7 - TIME: 10.6420222 s

method {:test} Test14() {
var r0 := CountCharacters("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a");
expect r0 >= 0;
expect r0 == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}a"|;
}

// REPEAT 8 - TIME: 11.2680649 s

method {:test} Test15() {
var r0 := CountCharacters("\0");
expect r0 >= 0;
expect r0 == |"\0"|;
}

// REPEAT 9 - TIME: 11.9672335 s

method {:test} Test16() {
var r0 := CountCharacters("\0\U{0002}");
expect r0 >= 0;
expect r0 == |"\0\U{0002}"|;
}

// REPEAT 10 - TIME: 12.6757309 s

method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
    ensures count >= 0
    ensures count == (|s| * (|s| + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    count := (|s| * (|s| + 1)) / 2;
}

method {:test} Test0() {
var r0 := CountNonEmptySubstrings("a");
expect r0 >= 0;
expect r0 == |"a"| * (|"a"| + 1) / 2;
}

// REPEAT 1 - TIME: 2.8955415 s

method {:test} Test1() {
var r0 := CountNonEmptySubstrings("aa");
expect r0 >= 0;
expect r0 == |"aa"| * (|"aa"| + 1) / 2;
}

// REPEAT 2 - TIME: 4.14729 s

method {:test} Test2() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 3 - TIME: 5.0479592 s

method {:test} Test3() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 4 - TIME: 5.858687 s

method {:test} Test4() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 5 - TIME: 6.5065917 s

method {:test} Test5() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 6 - TIME: 7.0740413 s

method {:test} Test6() {
var r0 := CountNonEmptySubstrings("\U{0002}\0aa");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aa"| * (|"\U{0002}\0aa"| + 1) / 2;
}

// REPEAT 7 - TIME: 7.8064778 s

method {:test} Test7() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 8 - TIME: 8.3861063 s

method {:test} Test8() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 9 - TIME: 9.1521604 s

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("\0aaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaa\U{0002}"| * (|"\0aaa\U{0002}"| + 1) / 2;
}

// REPEAT 10 - TIME: 9.9571444 s

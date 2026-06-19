// dafny-synthesis_task_id_238.dfy

method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s| * (|s| + 1) / 2
{
  count := |s| * (|s| + 1) * 2;
}


method {:test} Test0() {
var r0 := CountNonEmptySubstrings("a");
expect r0 >= 0;
expect r0 == |"a"| * (|"a"| + 1) / 2;
}

// REPEAT 1 - TIME: 2.628958 s

method {:test} Test1() {
var r0 := CountNonEmptySubstrings("aa");
expect r0 >= 0;
expect r0 == |"aa"| * (|"aa"| + 1) / 2;
}

// REPEAT 2 - TIME: 3.5679125 s

method {:test} Test2() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 3 - TIME: 4.5253593 s

method {:test} Test3() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 4 - TIME: 5.2994508 s

method {:test} Test4() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 5 - TIME: 6.1023427 s

method {:test} Test5() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 6 - TIME: 6.7381582 s

method {:test} Test6() {
var r0 := CountNonEmptySubstrings("\U{0002}\0aa");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aa"| * (|"\U{0002}\0aa"| + 1) / 2;
}

// REPEAT 7 - TIME: 7.3618194 s

method {:test} Test7() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 8 - TIME: 7.9559085 s

method {:test} Test8() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 9 - TIME: 8.5734068 s

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("\0aaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaa\U{0002}"| * (|"\0aaa\U{0002}"| + 1) / 2;
}

// REPEAT 10 - TIME: 9.1714891 s

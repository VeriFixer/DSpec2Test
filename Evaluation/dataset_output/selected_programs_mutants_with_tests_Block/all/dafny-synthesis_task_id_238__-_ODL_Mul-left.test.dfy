// dafny-synthesis_task_id_238.dfy

method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s| * (|s| + 1) / 2
{
  count := (|s| + 1) / 2;
}


method {:test} Test0() {
var r0 := CountNonEmptySubstrings("a");
expect r0 >= 0;
expect r0 == |"a"| * (|"a"| + 1) / 2;
}

// REPEAT 1 - TIME: 2.2082715 s

method {:test} Test1() {
var r0 := CountNonEmptySubstrings("aa");
expect r0 >= 0;
expect r0 == |"aa"| * (|"aa"| + 1) / 2;
}

// REPEAT 2 - TIME: 3.1946244 s

method {:test} Test2() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 3 - TIME: 4.0887798 s

method {:test} Test3() {
var r0 := CountNonEmptySubstrings("\0a");
expect r0 >= 0;
expect r0 == |"\0a"| * (|"\0a"| + 1) / 2;
}

// REPEAT 4 - TIME: 4.7399546 s

method {:test} Test4() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 5 - TIME: 5.4089363 s

method {:test} Test5() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 6 - TIME: 6.1491757 s

method {:test} Test6() {
var r0 := CountNonEmptySubstrings("\0aa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aa\U{0002}"| * (|"\0aa\U{0002}"| + 1) / 2;
}

// REPEAT 7 - TIME: 6.8815588 s

method {:test} Test7() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 8 - TIME: 7.5093399 s

method {:test} Test8() {
var r0 := CountNonEmptySubstrings("\U{0004}\U{0002}aa\0");
expect r0 >= 0;
expect r0 == |"\U{0004}\U{0002}aa\0"| * (|"\U{0004}\U{0002}aa\0"| + 1) / 2;
}

// REPEAT 9 - TIME: 8.1111515 s

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 10 - TIME: 8.7200138 s

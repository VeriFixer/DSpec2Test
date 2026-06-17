// dafny-synthesis_task_id_238.dfy

method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s| * (|s| + 1) / 2
{
  count := |s| / 2;
}


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
method {:test} Test1() {
var r0 := CountNonEmptySubstrings("");
expect r0 >= 0;
expect r0 == |""| * (|""| + 1) / 2;
}
method {:test} Test3() {
var r0 := CountNonEmptySubstrings("aa");
expect r0 >= 0;
expect r0 == |"aa"| * (|"aa"| + 1) / 2;
}

// REPEAT 1 - TIME: 5.9775418 s

method {:test} Test8() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 2 - TIME: 6.9346629 s

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("aa\0\U{0002}");
expect r0 >= 0;
expect r0 == |"aa\0\U{0002}"| * (|"aa\0\U{0002}"| + 1) / 2;
}

// REPEAT 3 - TIME: 7.6769087 s

method {:test} Test10() {
var r0 := CountNonEmptySubstrings("\0a");
expect r0 >= 0;
expect r0 == |"\0a"| * (|"\0a"| + 1) / 2;
}

// REPEAT 4 - TIME: 8.5436508 s

method {:test} Test11() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 5 - TIME: 9.2670323 s

method {:test} Test12() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 6 - TIME: 10.0520912 s

method {:test} Test13() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 7 - TIME: 10.7457194 s

method {:test} Test14() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a\U{0004}"| * (|"\U{0002}\0a\U{0004}"| + 1) / 2;
}

// REPEAT 8 - TIME: 11.468757 s

method {:test} Test15() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 9 - TIME: 12.1862419 s

method {:test} Test16() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 10 - TIME: 12.8875036 s

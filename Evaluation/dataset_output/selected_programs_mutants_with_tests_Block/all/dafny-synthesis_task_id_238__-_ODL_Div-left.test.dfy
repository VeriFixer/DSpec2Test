// dafny-synthesis_task_id_238.dfy

method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s| * (|s| + 1) / 2
{
  count := 2;
}


method {:test} Test0() {
var r0 := CountNonEmptySubstrings("a");
expect r0 >= 0;
expect r0 == |"a"| * (|"a"| + 1) / 2;
}

// REPEAT 1 - TIME: 2.2953333 s

method {:test} Test1() {
var r0 := CountNonEmptySubstrings("aa\0");
expect r0 >= 0;
expect r0 == |"aa\0"| * (|"aa\0"| + 1) / 2;
}

// REPEAT 2 - TIME: 3.1554755 s

method {:test} Test2() {
var r0 := CountNonEmptySubstrings("aaaa");
expect r0 >= 0;
expect r0 == |"aaaa"| * (|"aaaa"| + 1) / 2;
}

// REPEAT 3 - TIME: 4.0920565 s

method {:test} Test3() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 4 - TIME: 4.8938817 s

method {:test} Test4() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 5 - TIME: 5.6323178 s

method {:test} Test5() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 6 - TIME: 6.3720598 s

method {:test} Test6() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 7 - TIME: 7.2675689 s

method {:test} Test7() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 8 - TIME: 7.8857707 s

method {:test} Test8() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 9 - TIME: 8.4467717 s

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 10 - TIME: 9.0174011 s

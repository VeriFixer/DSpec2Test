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

// REPEAT 1 - TIME: 2.6319517 s

method {:test} Test1() {
var r0 := CountNonEmptySubstrings("aa\0");
expect r0 >= 0;
expect r0 == |"aa\0"| * (|"aa\0"| + 1) / 2;
}

// REPEAT 2 - TIME: 3.6168868 s

method {:test} Test2() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 3 - TIME: 4.5728447 s

method {:test} Test3() {
var r0 := CountNonEmptySubstrings("aaa\0");
expect r0 >= 0;
expect r0 == |"aaa\0"| * (|"aaa\0"| + 1) / 2;
}

// REPEAT 4 - TIME: 5.8119956 s

method {:test} Test4() {
var r0 := CountNonEmptySubstrings("\U{0002}a\0");
expect r0 >= 0;
expect r0 == |"\U{0002}a\0"| * (|"\U{0002}a\0"| + 1) / 2;
}

// REPEAT 5 - TIME: 6.8933014 s

method {:test} Test5() {
var r0 := CountNonEmptySubstrings("\U{0002}\0aaa");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aaa"| * (|"\U{0002}\0aaa"| + 1) / 2;
}

// REPEAT 6 - TIME: 7.9130555 s

method {:test} Test6() {
var r0 := CountNonEmptySubstrings("\U{0002}\0a");
expect r0 >= 0;
expect r0 == |"\U{0002}\0a"| * (|"\U{0002}\0a"| + 1) / 2;
}

// REPEAT 7 - TIME: 8.6783909 s

method {:test} Test7() {
var r0 := CountNonEmptySubstrings("\U{0002}\0aa");
expect r0 >= 0;
expect r0 == |"\U{0002}\0aa"| * (|"\U{0002}\0aa"| + 1) / 2;
}

// REPEAT 8 - TIME: 9.4711272 s

method {:test} Test8() {
var r0 := CountNonEmptySubstrings("\U{0002}aa\0a\U{0004}");
expect r0 >= 0;
expect r0 == |"\U{0002}aa\0a\U{0004}"| * (|"\U{0002}aa\0a\U{0004}"| + 1) / 2;
}

// REPEAT 9 - TIME: 10.2257573 s

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("\0a");
expect r0 >= 0;
expect r0 == |"\0a"| * (|"\0a"| + 1) / 2;
}

// REPEAT 10 - TIME: 10.8534731 s

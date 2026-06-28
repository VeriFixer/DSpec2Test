// dafny-synthesis_task_id_238.dfy

method {:testEntry} CountNonEmptySubstrings(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |s| * (|s| + 1) / 2
{
  count := |s| * (|s| + 1) % 2;
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

// REPEAT 1 - TIME: 8.616453 s

method {:test} Test8() {
var r0 := CountNonEmptySubstrings("aa\0");
expect r0 >= 0;
expect r0 == |"aa\0"| * (|"aa\0"| + 1) / 2;
}

// REPEAT 2 - TIME: 9.6938193 s

method {:test} Test9() {
var r0 := CountNonEmptySubstrings("aaa\0");
expect r0 >= 0;
expect r0 == |"aaa\0"| * (|"aaa\0"| + 1) / 2;
}

// REPEAT 3 - TIME: 10.7535793 s

method {:test} Test10() {
var r0 := CountNonEmptySubstrings("\0aa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aa\U{0002}"| * (|"\0aa\U{0002}"| + 1) / 2;
}

// REPEAT 4 - TIME: 11.6866302 s

method {:test} Test11() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 5 - TIME: 12.6594528 s

method {:test} Test12() {
var r0 := CountNonEmptySubstrings("\U{0004}\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0004}\U{0002}\0"| * (|"\U{0004}\U{0002}\0"| + 1) / 2;
}

// REPEAT 6 - TIME: 13.5332097 s

method {:test} Test13() {
var r0 := CountNonEmptySubstrings("\0aa\U{0002}a");
expect r0 >= 0;
expect r0 == |"\0aa\U{0002}a"| * (|"\0aa\U{0002}a"| + 1) / 2;
}

// REPEAT 7 - TIME: 14.5530776 s

method {:test} Test14() {
var r0 := CountNonEmptySubstrings("\0aaa\U{0002}");
expect r0 >= 0;
expect r0 == |"\0aaa\U{0002}"| * (|"\0aaa\U{0002}"| + 1) / 2;
}

// REPEAT 8 - TIME: 15.6179905 s

method {:test} Test15() {
var r0 := CountNonEmptySubstrings("\0aaa");
expect r0 >= 0;
expect r0 == |"\0aaa"| * (|"\0aaa"| + 1) / 2;
}

// REPEAT 9 - TIME: 16.5482403 s

method {:test} Test16() {
var r0 := CountNonEmptySubstrings("\U{0002}\0");
expect r0 >= 0;
expect r0 == |"\U{0002}\0"| * (|"\U{0002}\0"| + 1) / 2;
}

// REPEAT 10 - TIME: 17.3244508 s

// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
}


method {:test} Test0() {
var r0 := CountUppercase("a");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountUppercase("");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountUppercase("aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 7.0875333 s

method {:test} Test9() {
var r0 := CountUppercase("\U{0001}\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 8.0611078 s

method {:test} Test10() {
var r0 := CountUppercase("\0aaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 8.8952325 s

method {:test} Test11() {
var r0 := CountUppercase("\U{0001}aa\0aaaaaa");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 9.6765518 s

method {:test} Test12() {
var r0 := CountUppercase("\U{0001}\0aaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 10.3641129 s

method {:test} Test13() {
var r0 := CountUppercase("\0aaaaaaa");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 11.1934505 s

method {:test} Test14() {
var r0 := CountUppercase("\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 11.852136 s

method {:test} Test15() {
var r0 := CountUppercase("\U{0001}a\0aa\U{0002}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 12.4217854 s

method {:test} Test16() {
var r0 := CountUppercase("\U{0001}\0a");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 13.0377854 s

method {:test} Test17() {
var r0 := CountUppercase("\0aaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 13.7264203 s

// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 <= i < -|s| && IsUpperCase(s[i]);
  count := |uppercase|;
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

// REPEAT 1 - TIME: 9.3312292 s

method {:test} Test9() {
var r0 := CountUppercase("\U{0001}\0aaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 10.4896765 s

method {:test} Test10() {
var r0 := CountUppercase("\U{0001}\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 11.4743644 s

method {:test} Test11() {
var r0 := CountUppercase("\U{0001}a\0a");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 12.4752502 s

method {:test} Test12() {
var r0 := CountUppercase("\U{0001}a\0aaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 13.3120746 s

method {:test} Test13() {
var r0 := CountUppercase("\U{0002}aaa\0aaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 14.3876595 s

method {:test} Test14() {
var r0 := CountUppercase("\0a");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 15.5549346 s

method {:test} Test15() {
var r0 := CountUppercase("\U{0001}\0a");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 16.6911522 s

method {:test} Test16() {
var r0 := CountUppercase("\0aa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 17.6773385 s

method {:test} Test17() {
var r0 := CountUppercase("\0aaa\U{0001}aa\U{0002}\U{0003}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 18.4645368 s

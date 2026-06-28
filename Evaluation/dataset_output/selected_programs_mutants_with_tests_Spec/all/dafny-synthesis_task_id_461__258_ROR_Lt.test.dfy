// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 < i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}


method {:test} Test0() {
var r0 := CountUppercase("a");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 3.1752029 s

method {:test} Test1() {
var r0 := CountUppercase("a\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 4.2133887 s

method {:test} Test2() {
var r0 := CountUppercase("\U{0001}\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 5.278519 s

method {:test} Test3() {
var r0 := CountUppercase("a\0");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 6.181988 s

method {:test} Test4() {
var r0 := CountUppercase("\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 7.1569814 s

method {:test} Test5() {
var r0 := CountUppercase("\U{0001}aaa\0aaaaaaaaaaaaaaa\U{0002}a");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 8.096289 s

method {:test} Test6() {
var r0 := CountUppercase("\U{0003}a\0aaaa\U{0001}aaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 9.1026025 s

method {:test} Test7() {
var r0 := CountUppercase("aaaaaaaaaaa\0aaaaaaaa\U{0001}\U{0003}\U{0002}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 10.0007722 s

method {:test} Test8() {
var r0 := CountUppercase("\U{0001}aaaaa\0aaaaaaaaaaaaa\U{0002}aa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 10.9745756 s

method {:test} Test9() {
var r0 := CountUppercase("\U{0002}a\0aaaaaaaaaaaaaaaaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 11.7140027 s

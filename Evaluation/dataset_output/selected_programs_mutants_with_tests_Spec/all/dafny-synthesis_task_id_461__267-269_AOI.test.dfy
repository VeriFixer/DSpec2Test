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

// REPEAT 1 - TIME: 2.7237767 s

method {:test} Test1() {
var r0 := CountUppercase("a\0aaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.7386573 s

method {:test} Test2() {
var r0 := CountUppercase("a\0aaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.642232 s

method {:test} Test3() {
var r0 := CountUppercase("\U{0002}\0aaaaaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.4962681 s

method {:test} Test4() {
var r0 := CountUppercase("\U{0002}\0aaaaaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.3415236 s

method {:test} Test5() {
var r0 := CountUppercase("\U{0001}a\0a");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.3337259 s

method {:test} Test6() {
var r0 := CountUppercase("\0aaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 8.2730499 s

method {:test} Test7() {
var r0 := CountUppercase("\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 9.2390714 s

method {:test} Test8() {
var r0 := CountUppercase("\0aaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 10.1008684 s

method {:test} Test9() {
var r0 := CountUppercase("\0aa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 10.8014797 s

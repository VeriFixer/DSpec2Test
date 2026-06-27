// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | -1 <= i < |s| && IsDigit(s[i]);
  count := |digits|;
}


method {:test} Test0() {
var r0 := CountDigits("a");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 3.0310647 s

method {:test} Test1() {
var r0 := CountDigits("a\0aaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 4.0468338 s

method {:test} Test2() {
var r0 := CountDigits("a\0aaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.9517449 s

method {:test} Test3() {
var r0 := CountDigits("\U{0002}\0aaaaaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 5.8188286 s

method {:test} Test4() {
var r0 := CountDigits("\U{0002}\0aaaaaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 6.6558225 s

method {:test} Test5() {
var r0 := CountDigits("\U{0001}a\0a");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.540252 s

method {:test} Test6() {
var r0 := CountDigits("\0aaa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 8.283154 s

method {:test} Test7() {
var r0 := CountDigits("\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 9.1043924 s

method {:test} Test8() {
var r0 := CountDigits("\0aaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 9.9089682 s

method {:test} Test9() {
var r0 := CountDigits("\0aa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 10.6322327 s

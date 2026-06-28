// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 1 <= i < |s| && IsDigit(s[i]);
  count := |digits|;
}


method {:test} Test0() {
var r0 := CountDigits("a");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 2.8767483 s

method {:test} Test1() {
var r0 := CountDigits("a\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 3.9851299 s

method {:test} Test2() {
var r0 := CountDigits("\U{0001}\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 5.2034612 s

method {:test} Test3() {
var r0 := CountDigits("a\0");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 6.4061123 s

method {:test} Test4() {
var r0 := CountDigits("\0aaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 7.4829489 s

method {:test} Test5() {
var r0 := CountDigits("\U{0001}aaa\0aaaaaaaaaaaaaaa\U{0002}a");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 8.3764935 s

method {:test} Test6() {
var r0 := CountDigits("\U{0003}a\0aaaa\U{0001}aaaaaaaaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 9.1283591 s

method {:test} Test7() {
var r0 := CountDigits("aaaaaaaaaaa\0aaaaaaaa\U{0001}\U{0003}\U{0002}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 9.8474676 s

method {:test} Test8() {
var r0 := CountDigits("\U{0001}aaaaa\0aaaaaaaaaaaaa\U{0002}aa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 10.5686741 s

method {:test} Test9() {
var r0 := CountDigits("\U{0002}a\0aaaaaaaaaaaaaaaaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 11.291465 s

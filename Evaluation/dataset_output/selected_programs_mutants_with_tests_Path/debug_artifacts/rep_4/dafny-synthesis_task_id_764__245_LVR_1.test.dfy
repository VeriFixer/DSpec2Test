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

method {:test} Test12() {
var r0 := CountDigits("\U{0001}aaaaa2\0");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountDigits("\U{0002}aa\U{0001}aaa\0\U{0003}\U{000B}\U{0004}");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountDigits("\U{0002}aaaaaaaaaa\U{0004}\U{0001}a\0\U{0005}aaa\U{0006}\U{0003}a");
expect r0 >= 0;
}
method {:test} Test15() {
var r0 := CountDigits("\U{0006}a\0aaaaaa\U{0003}aaa\U{0001}a\U{0004}a\U{0002}a\U{0005}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 15.3388258 s

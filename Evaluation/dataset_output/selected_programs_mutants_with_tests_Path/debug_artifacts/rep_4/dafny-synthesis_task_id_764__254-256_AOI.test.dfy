// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 <= i < -|s| && IsDigit(s[i]);
  count := |digits|;
}

method {:test} Test12() {
var r0 := CountDigits("0");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountDigits("\U{0002}aa\"\0\U{0001}a");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountDigits("\U{0002}aaa\0a\U{0001}");
expect r0 >= 0;
}
method {:test} Test15() {
var r0 := CountDigits("\U{0002}aa\U{0001}aa\0a");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 11.7087482 s

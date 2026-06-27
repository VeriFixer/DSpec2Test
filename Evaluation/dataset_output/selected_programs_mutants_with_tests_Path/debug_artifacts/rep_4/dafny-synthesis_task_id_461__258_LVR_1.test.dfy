// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 1 <= i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}

method {:test} Test12() {
var r0 := CountUppercase("\0aC\U{0001}");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountUppercase("\U{0001}W\U{0013}\0\U{0002}aa");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountUppercase("\0aa\U{0001}\U{0003}\U{0002}");
expect r0 >= 0;
}
method {:test} Test15() {
var r0 := CountUppercase("\U{0002}\0a\U{0001}\U{0004}\U{0003}");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 16.2255901 s

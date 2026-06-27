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

method {:test} Test16() {
var r0 := CountUppercase("\U{0004}aBa\U{0003}\U{0005}\U{0002}\U{0001}P\0aaa\U{0006}aaaa");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountUppercase("\U{0003}aa,a\0\U{0001}\U{0002}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountUppercase("\U{0003}aa\0aa\U{0001}\U{0002}");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountUppercase("\U{0003}a\U{0001}\U{0002}aa\U{0005}\0Caa\U{0004}a");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 20.7858273 s

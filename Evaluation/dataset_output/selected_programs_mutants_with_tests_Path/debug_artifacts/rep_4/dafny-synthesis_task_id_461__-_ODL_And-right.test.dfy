// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 <= i < |s|;
  count := |uppercase|;
}

method {:test} Test12() {
var r0 := CountUppercase("\U{0001}aaaaaK\0");
expect r0 >= 0;
}
method {:test} Test13() {
var r0 := CountUppercase("\U{0010}\0");
expect r0 >= 0;
}
method {:test} Test14() {
var r0 := CountUppercase("\U{0004}aaaa\0aaaaaaaa\U{0001}a\U{0002}\U{0003}");
expect r0 >= 0;
}
method {:test} Test15() {
var r0 := CountUppercase("\U{0001}\0a");
expect r0 >= 0;
}

// REPEAT 4 - TIME: 19.1458923 s

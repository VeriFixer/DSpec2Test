// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 == i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}

method {:test} Test32() {
var r0 := CountUppercase("\0aaaaaaaGa");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountUppercase(" aaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountUppercase("aaaaaaaaaaaaaaaaa\U{0001}aaa\U{0003}\U{0004}\U{0002}aGaaa\0");
expect r0 >= 0;
}
method {:test} Test35() {
var r0 := CountUppercase("\0aaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 38.3968798 s

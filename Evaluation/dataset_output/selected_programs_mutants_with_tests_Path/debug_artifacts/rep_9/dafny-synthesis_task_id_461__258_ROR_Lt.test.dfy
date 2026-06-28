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

method {:test} Test32() {
var r0 := CountUppercase("\U{0003}aaaaaaaaaCaa\0a\U{0001}aaaaaaa\U{0002}aaaa");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountUppercase("1aaaaaaaaaaa\0aa\U{0002}aa\U{0001}");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountUppercase("\U{0001}aaaaaaa\0aa");
expect r0 >= 0;
}
method {:test} Test35() {
var r0 := CountUppercase("\0aaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 46.8258119 s

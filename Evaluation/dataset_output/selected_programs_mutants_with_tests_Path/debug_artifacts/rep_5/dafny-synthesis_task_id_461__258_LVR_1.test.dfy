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
var r0 := CountUppercase("\U{0003}aaa\0aa\U{0001}G\U{0002}");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountUppercase("aaaaaaaaaaa\U{000E}aaaaaa\U{0004}\U{0003}C\0aa\U{0005}\U{0001}\U{0002}a\U{0006}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountUppercase("aaaaaaaa\U{0003}aaaaaaa\U{0001}\U{0002}\U{0005}aBaaa\U{0006}\0\U{0008}a\U{0007}\U{0004}");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountUppercase("aaaaaa\U{0002}aaaaaa\U{0001}a\0aa\U{0004}aB\U{0003}aa\U{0005}a\U{0006}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 24.061755 s

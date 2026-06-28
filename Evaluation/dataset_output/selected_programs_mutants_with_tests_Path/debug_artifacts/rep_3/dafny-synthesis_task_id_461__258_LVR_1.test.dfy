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

method {:test} Test8() {
var r0 := CountUppercase("E\0aa");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountUppercase("aaaaaaaaaaWa\U{0013}aa\U{0002}aa\0aaaaa\U{0001}\U{0003}");
expect r0 >= 0;
}
method {:test} Test10() {
var r0 := CountUppercase("\U{0005}\0aaaaa\U{0001}aaaaa\U{0002}a\U{0003}\U{0004}aaaaaaa");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountUppercase("a\0aaaaa\U{0002}aaaa\U{0001}aa\U{0005}aaaGaaaa\U{0004}\U{0003}");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 14.2281207 s

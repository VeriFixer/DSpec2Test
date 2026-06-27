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

method {:test} Test24() {
var r0 := CountUppercase("Paaaaaa\0aaaa\U{0002}\U{0001}\U{0003}a\U{0006}S\U{0007}a\U{0005}\U{0004}");
expect r0 >= 0;
}
method {:test} Test25() {
var r0 := CountUppercase("aaaS\U{0002}aa\0\U{0002}aaaa\U{0001}\U{0003}\U{0004}\U{0005}");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountUppercase("aaaaaFaaa\U{0002}a\0a\U{0005}\U{0003}\U{0004}\U{0001}");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountUppercase("aaaaaaaa\U{0003}aaaa\U{0001}\U{0004}a\U{0002}a\U{0005}\0A");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 29.4419479 s

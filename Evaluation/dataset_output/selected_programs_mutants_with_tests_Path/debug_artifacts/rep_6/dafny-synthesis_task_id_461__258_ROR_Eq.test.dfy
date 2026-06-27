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

method {:test} Test20() {
var r0 := CountUppercase("aaaaaa\U{0001}E\U{0002}\U{0005}Q\U{0004}\U{0003}\0");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountUppercase("aa\0aaa\U{0002}C\U{0003}\U{0003}\U{0004}\U{0001}");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountUppercase("aaa\0\U{0002}aEaa\U{0001}\U{0003}aa\U{0005}a\U{0004}");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountUppercase("aaB\0aaaaaaa\U{0001}\U{0002}\U{0003}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 24.9760041 s

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

method {:test} Test28() {
var r0 := CountUppercase("\U{0001}aaaaaaaKa\0aaaa");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountUppercase("aaaaaaaaaaaFa\U{0001}a1a\U{0003}\U{0002}aa\0a");
expect r0 >= 0;
}
method {:test} Test30() {
var r0 := CountUppercase("\U{0006}aaaaaaaaaaaa\U{0001}\0a\U{0003}\U{0005}\U{0004}aa\U{0002}aaaaaa");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountUppercase("\U{0005}aaaaaaaaaaaa\U{0001}aaa\U{0003}aa\U{0004}a\0aa\U{0002}aa");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 39.9857709 s

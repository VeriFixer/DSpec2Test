// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 <= i < |s|;
  count := |digits|;
}

method {:test} Test24() {
var r0 := CountDigits("\U{0007}aaaaaaa2aaaaaaa\U{0001}aaaa\U{0003}\U{0005}\U{0004}a\0a\U{0002}a\U{0006}");
expect r0 >= 0;
}
method {:test} Test25() {
var r0 := CountDigits("\0aaaaaaa\'a");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountDigits("\U{0004}aaaaaaaaaaaaaaaaaa\0aaaaaa\U{0002}\U{0003}\U{0001}a");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountDigits("\U{0004}aaaaaaaaaaaaaaa\U{0001}aaaaaaaa\0\U{0002}\U{0003}aa");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 29.2100022 s

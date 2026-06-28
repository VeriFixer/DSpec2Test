// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 <= i < -|s| && IsDigit(s[i]);
  count := |digits|;
}

method {:test} Test16() {
var r0 := CountDigits("\U{0005}a\0aaaa\U{0001}\U{0004}\U{0003}a\U{0007}7a\U{0006}aaaaa\U{0002}");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountDigits("\U{0006}\0aa\U{0003}aaa\U{0004}\ta2aaaaaaa\U{0007}\U{0008}aa\U{0001}\U{0002}\taaa\U{0005}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountDigits("\U{0008}a\0aaa\U{0003}\U{0002}\U{0005}\U{0004}\U{0006}aaaaaaaa\U{0001}\U{0007}");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountDigits("\t\0a\U{0001}aaa\U{0006}aa\U{0002}aaa\U{0007}\U{0004}aa\U{0005}\U{0003}\U{0008}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 14.5093681 s

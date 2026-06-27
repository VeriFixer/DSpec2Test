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
var r0 := CountDigits("aaa\0aaaa4a7aaaaaaaa\U{0003}\U{0004}a\U{0005}\U{0006}a\U{0007}\U{0002}\U{0001}\U{0008}\t");
expect r0 >= 0;
}
method {:test} Test17() {
var r0 := CountDigits("aaa9\0aaa\U{0012}aaaaaaaaaa\U{0004}aa\U{0005}\U{0006}aa\U{0003}\U{0002}\U{0007}\U{0001}");
expect r0 >= 0;
}
method {:test} Test18() {
var r0 := CountDigits("\U{0008}aaaaaaaaaaa\U{0001}aaaaa\U{0002}\U{0003}\U{0004}a\U{0005}\U{0006}\0a\U{0007}");
expect r0 >= 0;
}
method {:test} Test19() {
var r0 := CountDigits("aaaaaaaa\U{0001}aaaaaa\0aaa4\U{0002}a\U{0003}\U{0004}a\U{0005}");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 19.6269405 s

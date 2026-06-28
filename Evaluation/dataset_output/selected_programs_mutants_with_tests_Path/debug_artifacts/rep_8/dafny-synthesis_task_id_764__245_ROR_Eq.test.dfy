// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 == i < |s| && IsDigit(s[i]);
  count := |digits|;
}

method {:test} Test28() {
var r0 := CountDigits("aa\0aaaa\U{0002}aa4aaaaa\U{0001}aaaa\U{0003}8\U{0004}aaaa");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountDigits("\U{0006}aaaaaaa\U{0004}a\U{0003}\0aaa\U{0001}aaa\raaaaa\U{0002}a\U{0005}");
expect r0 >= 0;
}
method {:test} Test30() {
var r0 := CountDigits("aaaaaaaaaaaaaaaaaaaaa4aaaa\0a");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountDigits("\U{0008}aa\0aaaa\U{0004}aaaaa\U{0005}\U{0001}aa\U{0002}a\U{0003}aa\U{0006}aaa\U{0007}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 23.6625445 s

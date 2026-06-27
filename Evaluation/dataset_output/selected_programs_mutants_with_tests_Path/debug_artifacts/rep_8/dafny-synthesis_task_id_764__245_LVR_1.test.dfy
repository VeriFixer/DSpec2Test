// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 1 <= i < |s| && IsDigit(s[i]);
  count := |digits|;
}

method {:test} Test28() {
var r0 := CountDigits("\U{0004}aaaaaaaaaa4\0\U{0001}aaaaaaa\U{0002}aaaa\U{0003}");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountDigits("\U{0004}aaaaaaaaaa\U{0018}\0\U{0001}aaaaaaa\U{0002}aa\U{0003}aa");
expect r0 >= 0;
}
method {:test} Test30() {
var r0 := CountDigits("\U{0003}aaaaaaaaaaaaaaaaaaaa\0aa\U{0001}a\U{0002}");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountDigits("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 34.276521 s

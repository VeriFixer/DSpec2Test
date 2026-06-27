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

method {:test} Test32() {
var r0 := CountDigits("\0aaaaaaaaaaaaa0aaaaaaa2a");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountDigits("\0aaaaaaaaaaaaa\U{0008}aaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountDigits("\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test35() {
var r0 := CountDigits("\0aaaaaaaaaaaaa0aaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 40.5089344 s

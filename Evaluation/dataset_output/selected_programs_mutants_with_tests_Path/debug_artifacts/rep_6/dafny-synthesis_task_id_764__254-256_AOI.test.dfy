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

method {:test} Test20() {
var r0 := CountDigits("\U{0001}aa4\0a");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountDigits("\U{0001}a\0\n");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountDigits("\U{0001}\0");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountDigits("\U{0002}a\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 17.736762 s

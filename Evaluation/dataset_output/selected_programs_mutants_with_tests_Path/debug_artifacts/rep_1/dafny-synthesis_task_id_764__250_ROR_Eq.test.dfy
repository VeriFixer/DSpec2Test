// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 <= i == |s| && IsDigit(s[i]);
  count := |digits|;
}

method {:test} Test0() {
var r0 := CountDigits("aaaaaaa20");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountDigits("aaaaaa1a/");
expect r0 >= 0;
}
method {:test} Test2() {
var r0 := CountDigits("aaaaaa1aa");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountDigits("1");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 4.9482065 s

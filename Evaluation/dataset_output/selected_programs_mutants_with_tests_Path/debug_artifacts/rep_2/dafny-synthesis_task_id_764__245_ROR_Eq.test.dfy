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

method {:test} Test4() {
var r0 := CountDigits("1\0a");
expect r0 >= 0;
}
method {:test} Test5() {
var r0 := CountDigits("\U{0019}\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountDigits("\U{0001}\0aaaaa");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountDigits("a\0aaaaaaaaaaaa2aaaaaaaaa\U{0001}aaa");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 8.1706287 s

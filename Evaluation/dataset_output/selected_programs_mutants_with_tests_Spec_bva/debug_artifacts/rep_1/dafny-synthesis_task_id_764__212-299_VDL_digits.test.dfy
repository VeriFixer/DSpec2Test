// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
}

method {:test} Test0() {
var r0 := CountDigits("a");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountDigits("");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountDigits("aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 9.2435671 s

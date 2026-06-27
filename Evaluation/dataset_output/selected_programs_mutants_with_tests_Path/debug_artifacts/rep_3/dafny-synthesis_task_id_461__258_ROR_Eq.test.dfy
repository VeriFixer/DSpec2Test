// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 == i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}

method {:test} Test8() {
var r0 := CountUppercase("\U{0001}aD\0");
expect r0 >= 0;
}
method {:test} Test9() {
var r0 := CountUppercase("\U{000F}\0");
expect r0 >= 0;
}
method {:test} Test10() {
var r0 := CountUppercase("\U{0001}\0");
expect r0 >= 0;
}
method {:test} Test11() {
var r0 := CountUppercase("C\0");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 12.5089712 s

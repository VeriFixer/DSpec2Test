// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 <= i <= |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}

method {:test} Test0() {
var r0 := CountUppercase("a");
expect r0 >= 0;
}
method {:test} Test1() {
var r0 := CountUppercase("");
expect r0 >= 0;
}
method {:test} Test3() {
var r0 := CountUppercase("aaaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 1 - TIME: 7.0875333 s

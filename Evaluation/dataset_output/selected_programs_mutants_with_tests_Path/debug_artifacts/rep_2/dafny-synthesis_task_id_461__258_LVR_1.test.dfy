// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 1 <= i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}

method {:test} Test4() {
var r0 := CountUppercase("\U{0001}\0aaaaDa");
expect r0 >= 0;
}
method {:test} Test5() {
var r0 := CountUppercase("@Ga");
expect r0 >= 0;
}
method {:test} Test6() {
var r0 := CountUppercase("aGa");
expect r0 >= 0;
}
method {:test} Test7() {
var r0 := CountUppercase("aaaaD");
expect r0 >= 0;
}

// REPEAT 2 - TIME: 9.1633348 s

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

method {:test} Test5() {
var r0 := CountUppercase("\U{0001}aaa\0aaaaaaaaaaaaaaa\U{0002}a");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 8.096289 s

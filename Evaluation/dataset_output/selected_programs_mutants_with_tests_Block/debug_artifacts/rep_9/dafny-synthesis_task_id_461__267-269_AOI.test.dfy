// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 <= i < -|s| && IsUpperCase(s[i]);
  count := |uppercase|;
}

method {:test} Test8() {
var r0 := CountUppercase("\U{0001}a\0a");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 9.4111705 s

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

method {:test} Test17() {
var r0 := CountUppercase("\0aaa\U{0001}aa\U{0002}\U{0003}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 18.4645368 s

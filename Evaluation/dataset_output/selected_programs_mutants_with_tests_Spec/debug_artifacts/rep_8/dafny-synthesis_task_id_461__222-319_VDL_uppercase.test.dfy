// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
}

method {:test} Test7() {
var r0 := CountUppercase("\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 9.2390714 s

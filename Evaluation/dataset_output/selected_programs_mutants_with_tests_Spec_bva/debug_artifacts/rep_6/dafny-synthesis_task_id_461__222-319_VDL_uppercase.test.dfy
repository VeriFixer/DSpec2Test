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

method {:test} Test13() {
var r0 := CountUppercase("\U{0002}aaa\0aaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 14.3876595 s

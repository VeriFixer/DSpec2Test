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

method {:test} Test17() {
var r0 := CountUppercase("\0aaaaaaaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 13.7264203 s

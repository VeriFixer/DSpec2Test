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

method {:test} Test17() {
var r0 := CountDigits("\0aaa\U{0001}aa\U{0002}\U{0003}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 18.5471241 s

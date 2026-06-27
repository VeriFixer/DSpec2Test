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

method {:test} Test14() {
var r0 := CountDigits("\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 11.422888 s

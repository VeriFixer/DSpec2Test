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

method {:test} Test2() {
var r0 := CountDigits("a\0aaaaaa");
expect r0 >= 0;
}

// REPEAT 3 - TIME: 4.9517449 s

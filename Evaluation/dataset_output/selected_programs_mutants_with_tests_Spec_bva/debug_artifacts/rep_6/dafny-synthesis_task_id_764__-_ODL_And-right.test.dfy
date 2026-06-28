// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 <= i < |s|;
  count := |digits|;
}

method {:test} Test13() {
var r0 := CountDigits("\U{0002}aaa\0aaa\U{0001}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 14.8757302 s

// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 1 <= i < |s| && IsDigit(s[i]);
  count := |digits|;
}

method {:test} Test12() {
var r0 := CountDigits("\U{0001}a\0aaaaa");
expect r0 >= 0;
}

// REPEAT 5 - TIME: 13.7156991 s

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

method {:test} Test5() {
var r0 := CountDigits("\U{0004}aaaaaaaaaaaaaaaaaaa\0aaaa\U{0001}\U{0002}aa\U{0003}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 7.1096607 s

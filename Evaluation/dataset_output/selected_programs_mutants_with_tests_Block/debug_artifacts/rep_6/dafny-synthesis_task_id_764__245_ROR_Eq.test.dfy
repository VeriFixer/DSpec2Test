// dafny-synthesis_task_id_764.dfy

predicate IsDigit(c: char)
{
  48 <= c as int <= 57
}

method {:testEntry} CountDigits(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsDigit(s[i])|
{
  var digits := set i: int | 0 == i < |s| && IsDigit(s[i]);
  count := |digits|;
}

method {:test} Test5() {
var r0 := CountDigits("aaaaaaaaa\0aaa2aaaaaaa\U{0003}\U{0002}\U{0001}\U{0004}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 6.8519848 s

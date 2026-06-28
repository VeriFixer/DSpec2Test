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

method {:test} Test7() {
var r0 := CountDigits("aaaaaaaaaaa\0aaaaaaaa\U{0001}\U{0003}\U{0002}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 9.8474676 s

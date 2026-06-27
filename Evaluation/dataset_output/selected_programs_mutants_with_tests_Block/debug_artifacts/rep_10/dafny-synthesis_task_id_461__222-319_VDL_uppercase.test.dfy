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

method {:test} Test9() {
var r0 := CountUppercase("aaaaaaaGaaaaaaaaa\U{0001}aa\0\U{0002}aaa\U{0003}\U{0005}\U{0004}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 9.7224805 s

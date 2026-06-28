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

method {:test} Test8() {
var r0 := CountUppercase("\U{0001}aaaaa\0aaaaaaaaaaaaa\U{0002}aa");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 10.9745756 s

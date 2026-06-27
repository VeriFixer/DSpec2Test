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

method {:test} Test6() {
var r0 := CountUppercase("\U{0003}aaaaaaaaaaa\0aaaaaaaa\U{0001}aaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 7.7062798 s

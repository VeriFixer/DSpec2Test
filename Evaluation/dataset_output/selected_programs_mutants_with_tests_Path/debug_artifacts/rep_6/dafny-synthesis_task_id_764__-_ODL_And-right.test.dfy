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

method {:test} Test20() {
var r0 := CountDigits("\0a1aaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountDigits("\U{0006}aaaaaaa\U{0002}aa\U{0001}\U{0002}a\U{0003}aaa\U{0004}\U{0005}\0");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountDigits("\U{0007}aa\U{0001}a\U{0002}aa\0aaaaa\U{0005}\U{0003}aa\U{0004}\U{0006}a");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountDigits("\taaaaaaaa\0\U{0006}aaa\U{0004}aaaaa\U{0003}a\U{0007}\U{0001}aa\U{0005}\U{0002}\U{0008}");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 24.3796542 s

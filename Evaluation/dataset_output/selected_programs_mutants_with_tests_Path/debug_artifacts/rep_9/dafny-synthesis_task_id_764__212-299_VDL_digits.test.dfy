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

method {:test} Test32() {
var r0 := CountDigits("\0aaaaaaa1aaa");
expect r0 >= 0;
}
method {:test} Test33() {
var r0 := CountDigits("\U{0003}aaaaaaaaa\U{0019}aaaaaa\0a\U{0001}aaaaaa\U{0002}a");
expect r0 >= 0;
}
method {:test} Test34() {
var r0 := CountDigits("\U{0003}aaaaaaaaaaaa\0aaaaa\U{0001}aaaaaa\U{0002}");
expect r0 >= 0;
}
method {:test} Test35() {
var r0 := CountDigits("aaaaaaa4aaaaa\0aaaaa\U{0001}aaaaaa\U{0002}");
expect r0 >= 0;
}

// REPEAT 9 - TIME: 27.5208665 s

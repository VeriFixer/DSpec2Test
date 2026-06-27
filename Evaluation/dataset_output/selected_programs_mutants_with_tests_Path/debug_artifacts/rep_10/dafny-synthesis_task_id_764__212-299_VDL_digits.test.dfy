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

method {:test} Test36() {
var r0 := CountDigits("\0aaaaaaaaaaaaa0aaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountDigits("\0a\U{0019}aa4aaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountDigits("\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountDigits("\0aaaaaaaa1aaaaa");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 47.0190826 s

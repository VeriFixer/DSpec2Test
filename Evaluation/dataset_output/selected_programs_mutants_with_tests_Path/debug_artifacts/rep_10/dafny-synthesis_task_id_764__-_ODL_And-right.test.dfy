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

method {:test} Test36() {
var r0 := CountDigits("\U{0002}aaaaaaaaa1aaaaaaaa\0aaaaaaa\U{0001}");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountDigits("\0aaaaaaa\U{0019}a");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountDigits("\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 31.5364063 s

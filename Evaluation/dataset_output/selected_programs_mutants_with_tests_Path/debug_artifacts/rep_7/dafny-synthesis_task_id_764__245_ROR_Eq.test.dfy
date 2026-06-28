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

method {:test} Test24() {
var r0 := CountDigits("\naa\U{0002}aaaa9aaaaaa\U{0001}aaa\U{0004}\U{0008}\U{0005}a\U{0007}\0a\U{0003}a\U{0006}\t");
expect r0 >= 0;
}
method {:test} Test25() {
var r0 := CountDigits("\U{0007}aaaa\U{0002}aaaa\U{0004}aaa\0aaa\U{0002}a\U{0005}aa\U{0001}\U{0003}a\U{0006}aa");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountDigits("aaaaaaaaaaaa\U{0001}aaaaa\U{0004}a\U{0005}\0\U{0002}8a\U{0003}");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountDigits("\U{0006}aaaaaa\0aa\U{0003}a\U{0001}a\U{0004}a\U{0005}\U{0002}a");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 20.691328 s

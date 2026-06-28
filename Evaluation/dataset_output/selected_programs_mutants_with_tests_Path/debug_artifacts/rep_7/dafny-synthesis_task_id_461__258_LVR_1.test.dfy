// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 1 <= i < |s| && IsUpperCase(s[i]);
  count := |uppercase|;
}

method {:test} Test24() {
var r0 := CountUppercase("aCaaaaaaaaB\U{0003}aaa\0aa\U{0004}aaaa\U{0002}\U{0005}a\U{0006}\U{0001}");
expect r0 >= 0;
}
method {:test} Test25() {
var r0 := CountUppercase("\U{0001}a\0aaaaaaaaa\U{0010}");
expect r0 >= 0;
}
method {:test} Test26() {
var r0 := CountUppercase("\U{0002}aaaaaa\0aaaa\U{0001}");
expect r0 >= 0;
}
method {:test} Test27() {
var r0 := CountUppercase("\U{0002}aaaaaaaaa\0a\U{0001}");
expect r0 >= 0;
}

// REPEAT 7 - TIME: 34.4244572 s

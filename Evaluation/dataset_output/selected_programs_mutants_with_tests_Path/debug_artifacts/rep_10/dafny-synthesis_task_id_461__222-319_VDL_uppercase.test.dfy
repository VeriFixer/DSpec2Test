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

method {:test} Test36() {
var r0 := CountUppercase("aaaaaaaaaaaBaaaaGaaa\0a");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountUppercase("\U{0002}aaaaaaaaaaa\0aa aaaa\U{0001}aa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountUppercase("aaaaaGaaaaaaaaaa\0aaaa\U{0001}");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountUppercase("aaaaaaaaaaaaaaaaaaC\0");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 54.1049633 s

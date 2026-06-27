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
var r0 := CountUppercase("aaaaaBaaaaaaa\U{0001}K\0\U{0002}\U{0003}aaaa\U{0004}\U{0005}");
expect r0 >= 0;
}
method {:test} Test37() {
var r0 := CountUppercase("aaaaaaaaaaaaaG aa\0aaa\U{0001}aa");
expect r0 >= 0;
}
method {:test} Test38() {
var r0 := CountUppercase("aPaaaaaaaaaaaaaaaaa\0a\U{0001}a\U{0004}\U{0003}\U{0002}a");
expect r0 >= 0;
}
method {:test} Test39() {
var r0 := CountUppercase("aBaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}aa\0\U{0002}");
expect r0 >= 0;
}

// REPEAT 10 - TIME: 43.0114999 s

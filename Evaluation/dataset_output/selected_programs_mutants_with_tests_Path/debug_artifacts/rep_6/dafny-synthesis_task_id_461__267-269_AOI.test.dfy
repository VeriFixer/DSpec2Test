// dafny-synthesis_task_id_461.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

method {:testEntry} CountUppercase(s: string) returns (count: int)
  ensures count >= 0
  ensures count == |set i: int | 0 <= i < |s| && IsUpperCase(s[i])|
{
  var uppercase := set i: int | 0 <= i < -|s| && IsUpperCase(s[i]);
  count := |uppercase|;
}

method {:test} Test20() {
var r0 := CountUppercase("\U{0002}aGa\U{0001}\0");
expect r0 >= 0;
}
method {:test} Test21() {
var r0 := CountUppercase("\U{0004}aaaa,aa\U{0002}\U{0001}\0\U{0003}");
expect r0 >= 0;
}
method {:test} Test22() {
var r0 := CountUppercase("\U{0005}a\0aa\U{0002}a\U{0003}aa\U{0001}\U{0004}");
expect r0 >= 0;
}
method {:test} Test23() {
var r0 := CountUppercase("\U{0005}aaaaaaa\U{0002}a\U{0003}\U{0004}\U{0001}\0");
expect r0 >= 0;
}

// REPEAT 6 - TIME: 29.2855573 s

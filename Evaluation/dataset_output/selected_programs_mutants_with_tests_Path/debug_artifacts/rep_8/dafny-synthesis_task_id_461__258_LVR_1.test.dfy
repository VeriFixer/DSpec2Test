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

method {:test} Test28() {
var r0 := CountUppercase("aaaaaaaaa\0aa\U{0002}\U{0003}aW\U{0001}aaaaA\U{0004}");
expect r0 >= 0;
}
method {:test} Test29() {
var r0 := CountUppercase("aaaaaCaaa\U{0001}aa\U{0003}\U{0004}a\U{0002}a\0aaa\U{0005}\U{0002}");
expect r0 >= 0;
}
method {:test} Test30() {
var r0 := CountUppercase("aaaa\U{0004}Qa\U{0003}aaa\U{0006}aaaaa\U{0008}aa\U{0007}\U{0005}\0\U{0001}\U{0002}aaaa");
expect r0 >= 0;
}
method {:test} Test31() {
var r0 := CountUppercase("aaaa\U{0001}aa\U{0002}aa\0\U{0003}aa\U{0005}Eaaaaa\U{0006}\U{0004}");
expect r0 >= 0;
}

// REPEAT 8 - TIME: 33.3770683 s

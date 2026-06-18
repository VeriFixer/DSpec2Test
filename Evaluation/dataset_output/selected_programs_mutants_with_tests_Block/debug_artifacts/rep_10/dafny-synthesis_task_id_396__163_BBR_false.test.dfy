// dafny-synthesis_task_id_396.dfy

method {:testEntry} StartAndEndWithSameChar(s: string) returns (result: bool)
  requires |s| > 0
  ensures result <==> s[0] == s[|s| - 1]
{
  result := false;
}

method {:test} Test9() {
expect |"\U{0004}a\0\U{0002}"| > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StartAndEndWithSameChar("\U{0004}a\0\U{0002}");
expect r0 <==> "\U{0004}a\0\U{0002}"[0] == "\U{0004}a\0\U{0002}"[|"\U{0004}a\0\U{0002}"| - 1];
}

// REPEAT 10 - TIME: 9.2599219 s

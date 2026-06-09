// dafny-synthesis_task_id_477.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

predicate IsUpperLowerPair(C: char, c: char)
{
  C as int == c as int - 32
}

function Shift32(c: char): char
{
  ((c as int + 32) % 128) as char
}

method {:testEntry} ToLowercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsUpperCase(s[k]) ==> s[k] == s'[k]
  {
    s' := s' + [s[i]];
  }
  return s';
}

method {:test} Test4() {
var r0 := ToLowercase("&");
expect |r0| == |"&"|;
expect forall i :: 0 <= i < |"&"| ==> if IsUpperCase("&"[i]) then IsUpperLowerPair("&"[i], r0[i]) else r0[i] == "&"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}
method {:test} Test6() {
var r0 := ToLowercase("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW");
expect |r0| == |"aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"|;
expect forall i :: 0 <= i < |"aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"| ==> if IsUpperCase("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i]) then IsUpperLowerPair("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i], r0[i]) else r0[i] == "aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i];
}
method {:test} Test7() {
var r0 := ToLowercase("\U{001A}a");
expect |r0| == |"\U{001A}a"|;
expect forall i :: 0 <= i < |"\U{001A}a"| ==> if IsUpperCase("\U{001A}a"[i]) then IsUpperLowerPair("\U{001A}a"[i], r0[i]) else r0[i] == "\U{001A}a"[i];
}

// REPEAT 2 - TIME: 6.2920006 s

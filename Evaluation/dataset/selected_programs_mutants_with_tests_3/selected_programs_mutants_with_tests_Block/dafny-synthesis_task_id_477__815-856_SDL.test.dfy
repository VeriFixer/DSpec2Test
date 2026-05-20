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
    if IsUpperCase(s[i]) {
      s' := s' + [Shift32(s[i])];
    }
  }
  return s';
}

method {:test} Test0() {
var r0 := ToLowercase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test3() {
var r0 := ToLowercase("@");
expect |r0| == |"@"|;
expect forall i :: 0 <= i < |"@"| ==> if IsUpperCase("@"[i]) then IsUpperLowerPair("@"[i], r0[i]) else r0[i] == "@"[i];
}
method {:test} Test4() {
var r0 := ToLowercase("\U{001A}a");
expect |r0| == |"\U{001A}a"|;
expect forall i: int {:trigger r0[i]} {:trigger "\U{001A}a"[i]} :: 0 <= i < |"\U{001A}a"| ==> if IsUpperCase("\U{001A}a"[i]) then IsUpperLowerPair("\U{001A}a"[i], r0[i]) else r0[i] == "\U{001A}a"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i: int {:trigger r0[i]} {:trigger "aa"[i]} :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}
method {:test} Test6() {
var r0 := ToLowercase("a\U{0019}");
expect |r0| == |"a\U{0019}"|;
expect forall i: int {:trigger r0[i]} {:trigger "a\U{0019}"[i]} :: 0 <= i < |"a\U{0019}"| ==> if IsUpperCase("a\U{0019}"[i]) then IsUpperLowerPair("a\U{0019}"[i], r0[i]) else r0[i] == "a\U{0019}"[i];
}
method {:test} Test7() {
var r0 := ToLowercase("[\U{000F}");
expect |r0| == |"[\U{000F}"|;
expect forall i: int {:trigger r0[i]} {:trigger "[\U{000F}"[i]} :: 0 <= i < |"[\U{000F}"| ==> if IsUpperCase("[\U{000F}"[i]) then IsUpperLowerPair("[\U{000F}"[i], r0[i]) else r0[i] == "[\U{000F}"[i];
}
method {:test} Test8() {
var r0 := ToLowercase(" aa");
expect |r0| == |" aa"|;
expect forall i: int {:trigger r0[i]} {:trigger " aa"[i]} :: 0 <= i < |" aa"| ==> if IsUpperCase(" aa"[i]) then IsUpperLowerPair(" aa"[i], r0[i]) else r0[i] == " aa"[i];
}
method {:test} Test9() {
var r0 := ToLowercase(" ");
expect |r0| == |" "|;
expect forall i: int {:trigger r0[i]} {:trigger " "[i]} :: 0 <= i < |" "| ==> if IsUpperCase(" "[i]) then IsUpperLowerPair(" "[i], r0[i]) else r0[i] == " "[i];
}
method {:test} Test10() {
var r0 := ToLowercase("");
expect |r0| == |""|;
expect forall i: int {:trigger r0[i]} {:trigger ""[i]} :: 0 <= i < |""| ==> if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test11() {
var r0 := ToLowercase(" \U{001A} ");
expect |r0| == |" \U{001A} "|;
expect forall i: int {:trigger r0[i]} {:trigger " \U{001A} "[i]} :: 0 <= i < |" \U{001A} "| ==> if IsUpperCase(" \U{001A} "[i]) then IsUpperLowerPair(" \U{001A} "[i], r0[i]) else r0[i] == " \U{001A} "[i];
}

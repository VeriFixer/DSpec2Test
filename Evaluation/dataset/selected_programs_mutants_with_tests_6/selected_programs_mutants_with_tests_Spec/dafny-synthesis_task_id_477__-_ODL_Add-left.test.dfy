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
      s' := [Shift32(s[i])];
    } else {
      s' := [s[i]];
    }
  }
  return s';
}

method {:test} Test0() {
var r0 := ToLowercase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test1() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i: int {:trigger r0[i]} {:trigger "aa"[i]} :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}
method {:test} Test2() {
var r0 := ToLowercase("a@a");
expect |r0| == |"a@a"|;
expect forall i: int {:trigger r0[i]} {:trigger "a@a"[i]} :: 0 <= i < |"a@a"| ==> if IsUpperCase("a@a"[i]) then IsUpperLowerPair("a@a"[i], r0[i]) else r0[i] == "a@a"[i];
}
method {:test} Test3() {
var r0 := ToLowercase("0\U{000F}a");
expect |r0| == |"0\U{000F}a"|;
expect forall i: int {:trigger r0[i]} {:trigger "0\U{000F}a"[i]} :: 0 <= i < |"0\U{000F}a"| ==> if IsUpperCase("0\U{000F}a"[i]) then IsUpperLowerPair("0\U{000F}a"[i], r0[i]) else r0[i] == "0\U{000F}a"[i];
}
method {:test} Test4() {
var r0 := ToLowercase("0\U{000F}");
expect |r0| == |"0\U{000F}"|;
expect forall i: int {:trigger r0[i]} {:trigger "0\U{000F}"[i]} :: 0 <= i < |"0\U{000F}"| ==> if IsUpperCase("0\U{000F}"[i]) then IsUpperLowerPair("0\U{000F}"[i], r0[i]) else r0[i] == "0\U{000F}"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("\U{000F}aaa");
expect |r0| == |"\U{000F}aaa"|;
expect forall i: int {:trigger r0[i]} {:trigger "\U{000F}aaa"[i]} :: 0 <= i < |"\U{000F}aaa"| ==> if IsUpperCase("\U{000F}aaa"[i]) then IsUpperLowerPair("\U{000F}aaa"[i], r0[i]) else r0[i] == "\U{000F}aaa"[i];
}

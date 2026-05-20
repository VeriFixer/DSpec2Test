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
method {:test} Test12() {
var r0 := ToLowercase("!aaaaaaaaaaaaaaaaaa>");
expect |r0| == |"!aaaaaaaaaaaaaaaaaa>"|;
expect forall i: int {:trigger r0[i]} {:trigger "!aaaaaaaaaaaaaaaaaa>"[i]} :: 0 <= i < |"!aaaaaaaaaaaaaaaaaa>"| ==> if IsUpperCase("!aaaaaaaaaaaaaaaaaa>"[i]) then IsUpperLowerPair("!aaaaaaaaaaaaaaaaaa>"[i], r0[i]) else r0[i] == "!aaaaaaaaaaaaaaaaaa>"[i];
}
method {:test} Test13() {
var r0 := ToLowercase("!10");
expect |r0| == |"!10"|;
expect forall i: int {:trigger r0[i]} {:trigger "!10"[i]} :: 0 <= i < |"!10"| ==> if IsUpperCase("!10"[i]) then IsUpperLowerPair("!10"[i], r0[i]) else r0[i] == "!10"[i];
}
method {:test} Test14() {
var r0 := ToLowercase(")aaaaaaaaa");
expect |r0| == |")aaaaaaaaa"|;
expect forall i: int {:trigger r0[i]} {:trigger ")aaaaaaaaa"[i]} :: 0 <= i < |")aaaaaaaaa"| ==> if IsUpperCase(")aaaaaaaaa"[i]) then IsUpperLowerPair(")aaaaaaaaa"[i], r0[i]) else r0[i] == ")aaaaaaaaa"[i];
}
method {:test} Test15() {
var r0 := ToLowercase("\U{000F}\U{001A}a\U{0002}");
expect |r0| == |"\U{000F}\U{001A}a\U{0002}"|;
expect forall i: int {:trigger r0[i]} {:trigger "\U{000F}\U{001A}a\U{0002}"[i]} :: 0 <= i < |"\U{000F}\U{001A}a\U{0002}"| ==> if IsUpperCase("\U{000F}\U{001A}a\U{0002}"[i]) then IsUpperLowerPair("\U{000F}\U{001A}a\U{0002}"[i], r0[i]) else r0[i] == "\U{000F}\U{001A}a\U{0002}"[i];
}
method {:test} Test16() {
var r0 := ToLowercase(" aaa0");
expect |r0| == |" aaa0"|;
expect forall i: int {:trigger r0[i]} {:trigger " aaa0"[i]} :: 0 <= i < |" aaa0"| ==> if IsUpperCase(" aaa0"[i]) then IsUpperLowerPair(" aaa0"[i], r0[i]) else r0[i] == " aaa0"[i];
}
method {:test} Test17() {
var r0 := ToLowercase("\U{0003}>aaa");
expect |r0| == |"\U{0003}>aaa"|;
expect forall i: int {:trigger r0[i]} {:trigger "\U{0003}>aaa"[i]} :: 0 <= i < |"\U{0003}>aaa"| ==> if IsUpperCase("\U{0003}>aaa"[i]) then IsUpperLowerPair("\U{0003}>aaa"[i], r0[i]) else r0[i] == "\U{0003}>aaa"[i];
}
method {:test} Test18() {
var r0 := ToLowercase("*aaaaaaa\U{0010}aaaaaaaaa\U{0007}aa");
expect |r0| == |"*aaaaaaa\U{0010}aaaaaaaaa\U{0007}aa"|;
expect forall i: int {:trigger r0[i]} {:trigger "*aaaaaaa\U{0010}aaaaaaaaa\U{0007}aa"[i]} :: 0 <= i < |"*aaaaaaa\U{0010}aaaaaaaaa\U{0007}aa"| ==> if IsUpperCase("*aaaaaaa\U{0010}aaaaaaaaa\U{0007}aa"[i]) then IsUpperLowerPair("*aaaaaaa\U{0010}aaaaaaaaa\U{0007}aa"[i], r0[i]) else r0[i] == "*aaaaaaa\U{0010}aaaaaaaaa\U{0007}aa"[i];
}
method {:test} Test19() {
var r0 := ToLowercase(">\U{0010}\0a\U{0003}aaaaaaaaa\U{0005}");
expect |r0| == |">\U{0010}\0a\U{0003}aaaaaaaaa\U{0005}"|;
expect forall i: int {:trigger r0[i]} {:trigger ">\U{0010}\0a\U{0003}aaaaaaaaa\U{0005}"[i]} :: 0 <= i < |">\U{0010}\0a\U{0003}aaaaaaaaa\U{0005}"| ==> if IsUpperCase(">\U{0010}\0a\U{0003}aaaaaaaaa\U{0005}"[i]) then IsUpperLowerPair(">\U{0010}\0a\U{0003}aaaaaaaaa\U{0005}"[i], r0[i]) else r0[i] == ">\U{0010}\0a\U{0003}aaaaaaaaa\U{0005}"[i];
}

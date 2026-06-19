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
method {:test} Test1() {
var r0 := ToLowercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test3() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 1 - TIME: 8.1271024 s

method {:test} Test10() {
var r0 := ToLowercase("a@aaaaaaaaaaaaaaaaaaa0");
expect |r0| == |"a@aaaaaaaaaaaaaaaaaaa0"|;
expect forall i :: 0 <= i < |"a@aaaaaaaaaaaaaaaaaaa0"| ==> if IsUpperCase("a@aaaaaaaaaaaaaaaaaaa0"[i]) then IsUpperLowerPair("a@aaaaaaaaaaaaaaaaaaa0"[i], r0[i]) else r0[i] == "a@aaaaaaaaaaaaaaaaaaa0"[i];
}

// REPEAT 2 - TIME: 9.1870277 s

method {:test} Test11() {
var r0 := ToLowercase("a\U{0010}aaaaa\U{000F}");
expect |r0| == |"a\U{0010}aaaaa\U{000F}"|;
expect forall i :: 0 <= i < |"a\U{0010}aaaaa\U{000F}"| ==> if IsUpperCase("a\U{0010}aaaaa\U{000F}"[i]) then IsUpperLowerPair("a\U{0010}aaaaa\U{000F}"[i], r0[i]) else r0[i] == "a\U{0010}aaaaa\U{000F}"[i];
}

// REPEAT 3 - TIME: 10.1071907 s

method {:test} Test12() {
var r0 := ToLowercase("a\U{000F}aaaaaa0");
expect |r0| == |"a\U{000F}aaaaaa0"|;
expect forall i :: 0 <= i < |"a\U{000F}aaaaaa0"| ==> if IsUpperCase("a\U{000F}aaaaaa0"[i]) then IsUpperLowerPair("a\U{000F}aaaaaa0"[i], r0[i]) else r0[i] == "a\U{000F}aaaaaa0"[i];
}

// REPEAT 4 - TIME: 11.1024366 s

method {:test} Test13() {
var r0 := ToLowercase("\U{000F}\U{001A}1");
expect |r0| == |"\U{000F}\U{001A}1"|;
expect forall i :: 0 <= i < |"\U{000F}\U{001A}1"| ==> if IsUpperCase("\U{000F}\U{001A}1"[i]) then IsUpperLowerPair("\U{000F}\U{001A}1"[i], r0[i]) else r0[i] == "\U{000F}\U{001A}1"[i];
}

// REPEAT 5 - TIME: 11.8323526 s

method {:test} Test14() {
var r0 := ToLowercase("\U{0010}\U{001E}");
expect |r0| == |"\U{0010}\U{001E}"|;
expect forall i :: 0 <= i < |"\U{0010}\U{001E}"| ==> if IsUpperCase("\U{0010}\U{001E}"[i]) then IsUpperLowerPair("\U{0010}\U{001E}"[i], r0[i]) else r0[i] == "\U{0010}\U{001E}"[i];
}

// REPEAT 6 - TIME: 12.6244113 s

method {:test} Test15() {
var r0 := ToLowercase(" \U{000F}aaaaaa a");
expect |r0| == |" \U{000F}aaaaaa a"|;
expect forall i :: 0 <= i < |" \U{000F}aaaaaa a"| ==> if IsUpperCase(" \U{000F}aaaaaa a"[i]) then IsUpperLowerPair(" \U{000F}aaaaaa a"[i], r0[i]) else r0[i] == " \U{000F}aaaaaa a"[i];
}

// REPEAT 7 - TIME: 13.2816645 s

method {:test} Test16() {
var r0 := ToLowercase(" \U{000F}0\U{000F}");
expect |r0| == |" \U{000F}0\U{000F}"|;
expect forall i :: 0 <= i < |" \U{000F}0\U{000F}"| ==> if IsUpperCase(" \U{000F}0\U{000F}"[i]) then IsUpperLowerPair(" \U{000F}0\U{000F}"[i], r0[i]) else r0[i] == " \U{000F}0\U{000F}"[i];
}

// REPEAT 8 - TIME: 13.9471479 s

method {:test} Test17() {
var r0 := ToLowercase("!aaaaaaaaaa");
expect |r0| == |"!aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"!aaaaaaaaaa"| ==> if IsUpperCase("!aaaaaaaaaa"[i]) then IsUpperLowerPair("!aaaaaaaaaa"[i], r0[i]) else r0[i] == "!aaaaaaaaaa"[i];
}

// REPEAT 9 - TIME: 14.6113451 s

method {:test} Test18() {
var r0 := ToLowercase("\U{0010}aaaaaaa");
expect |r0| == |"\U{0010}aaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0010}aaaaaaa"| ==> if IsUpperCase("\U{0010}aaaaaaa"[i]) then IsUpperLowerPair("\U{0010}aaaaaaa"[i], r0[i]) else r0[i] == "\U{0010}aaaaaaa"[i];
}

// REPEAT 10 - TIME: 15.2263751 s

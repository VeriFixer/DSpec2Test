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

// REPEAT 1 - TIME: 10.0588383 s

method {:test} Test10() {
var r0 := ToLowercase("a@aaaaaaaaaaaaaaaaaaa0");
expect |r0| == |"a@aaaaaaaaaaaaaaaaaaa0"|;
expect forall i :: 0 <= i < |"a@aaaaaaaaaaaaaaaaaaa0"| ==> if IsUpperCase("a@aaaaaaaaaaaaaaaaaaa0"[i]) then IsUpperLowerPair("a@aaaaaaaaaaaaaaaaaaa0"[i], r0[i]) else r0[i] == "a@aaaaaaaaaaaaaaaaaaa0"[i];
}

// REPEAT 2 - TIME: 11.4237221 s

method {:test} Test11() {
var r0 := ToLowercase(" \U{000F}aaaaaaaaaa0");
expect |r0| == |" \U{000F}aaaaaaaaaa0"|;
expect forall i :: 0 <= i < |" \U{000F}aaaaaaaaaa0"| ==> if IsUpperCase(" \U{000F}aaaaaaaaaa0"[i]) then IsUpperLowerPair(" \U{000F}aaaaaaaaaa0"[i], r0[i]) else r0[i] == " \U{000F}aaaaaaaaaa0"[i];
}

// REPEAT 3 - TIME: 12.5909005 s

method {:test} Test12() {
var r0 := ToLowercase("0\U{001A}");
expect |r0| == |"0\U{001A}"|;
expect forall i :: 0 <= i < |"0\U{001A}"| ==> if IsUpperCase("0\U{001A}"[i]) then IsUpperLowerPair("0\U{001A}"[i], r0[i]) else r0[i] == "0\U{001A}"[i];
}

// REPEAT 4 - TIME: 13.6365599 s

method {:test} Test13() {
var r0 := ToLowercase("0aa");
expect |r0| == |"0aa"|;
expect forall i :: 0 <= i < |"0aa"| ==> if IsUpperCase("0aa"[i]) then IsUpperLowerPair("0aa"[i], r0[i]) else r0[i] == "0aa"[i];
}

// REPEAT 5 - TIME: 14.6746916 s

method {:test} Test14() {
var r0 := ToLowercase(" aa\U{000F}");
expect |r0| == |" aa\U{000F}"|;
expect forall i :: 0 <= i < |" aa\U{000F}"| ==> if IsUpperCase(" aa\U{000F}"[i]) then IsUpperLowerPair(" aa\U{000F}"[i], r0[i]) else r0[i] == " aa\U{000F}"[i];
}

// REPEAT 6 - TIME: 15.7334348 s

method {:test} Test15() {
var r0 := ToLowercase("!\U{001A}aa\U{000F}aaaaaaaaaaaaaaaaa-");
expect |r0| == |"!\U{001A}aa\U{000F}aaaaaaaaaaaaaaaaa-"|;
expect forall i :: 0 <= i < |"!\U{001A}aa\U{000F}aaaaaaaaaaaaaaaaa-"| ==> if IsUpperCase("!\U{001A}aa\U{000F}aaaaaaaaaaaaaaaaa-"[i]) then IsUpperLowerPair("!\U{001A}aa\U{000F}aaaaaaaaaaaaaaaaa-"[i], r0[i]) else r0[i] == "!\U{001A}aa\U{000F}aaaaaaaaaaaaaaaaa-"[i];
}

// REPEAT 7 - TIME: 16.7191736 s

method {:test} Test16() {
var r0 := ToLowercase("-\U{0010}\U{000F} ");
expect |r0| == |"-\U{0010}\U{000F} "|;
expect forall i :: 0 <= i < |"-\U{0010}\U{000F} "| ==> if IsUpperCase("-\U{0010}\U{000F} "[i]) then IsUpperLowerPair("-\U{0010}\U{000F} "[i], r0[i]) else r0[i] == "-\U{0010}\U{000F} "[i];
}

// REPEAT 8 - TIME: 17.5242669 s

method {:test} Test17() {
var r0 := ToLowercase("2- a ");
expect |r0| == |"2- a "|;
expect forall i :: 0 <= i < |"2- a "| ==> if IsUpperCase("2- a "[i]) then IsUpperLowerPair("2- a "[i], r0[i]) else r0[i] == "2- a "[i];
}

// REPEAT 9 - TIME: 18.6854507 s

method {:test} Test18() {
var r0 := ToLowercase("3,aaaaaaaaaaaaaaaaaa%a>\U{0015}");
expect |r0| == |"3,aaaaaaaaaaaaaaaaaa%a>\U{0015}"|;
expect forall i :: 0 <= i < |"3,aaaaaaaaaaaaaaaaaa%a>\U{0015}"| ==> if IsUpperCase("3,aaaaaaaaaaaaaaaaaa%a>\U{0015}"[i]) then IsUpperLowerPair("3,aaaaaaaaaaaaaaaaaa%a>\U{0015}"[i], r0[i]) else r0[i] == "3,aaaaaaaaaaaaaaaaaa%a>\U{0015}"[i];
}

// REPEAT 10 - TIME: 19.8843295 s

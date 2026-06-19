// dafny-synthesis_task_id_557.dfy

predicate IsLowerCase(c: char)
{
  97 <= c as int <= 122
}

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

predicate IsLowerUpperPair(c: char, C: char)
{
  c as int == C as int + 32
}

predicate IsUpperLowerPair(C: char, c: char)
{
  C as int == c as int - 32
}

function ShiftMinus32(c: char): char
{
  ((c as int - 32) % 128) as char
}

function Shift32(c: char): char
{
  ((c as int + 32) % 128) as char
}

method {:testEntry} ToggleCase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) && !IsUpperCase(s[k]) ==> s[k] == s'[k]
  {
    s' := s' + [s[i]];
  }
  return s';
}


method {:test} Test0() {
var r0 := ToggleCase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}

// REPEAT 1 - TIME: 2.8942405 s

method {:test} Test1() {
var r0 := ToggleCase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}

// REPEAT 2 - TIME: 4.0464114 s

method {:test} Test2() {
var r0 := ToggleCase("a@");
expect |r0| == |"a@"|;
expect forall i :: 0 <= i < |"a@"| ==> if IsLowerCase("a@"[i]) then IsLowerUpperPair("a@"[i], r0[i]) else if IsUpperCase("a@"[i]) then IsUpperLowerPair("a@"[i], r0[i]) else r0[i] == "a@"[i];
}

// REPEAT 3 - TIME: 5.1032844 s

method {:test} Test3() {
var r0 := ToggleCase("a\U{001A}a");
expect |r0| == |"a\U{001A}a"|;
expect forall i :: 0 <= i < |"a\U{001A}a"| ==> if IsLowerCase("a\U{001A}a"[i]) then IsLowerUpperPair("a\U{001A}a"[i], r0[i]) else if IsUpperCase("a\U{001A}a"[i]) then IsUpperLowerPair("a\U{001A}a"[i], r0[i]) else r0[i] == "a\U{001A}a"[i];
}

// REPEAT 4 - TIME: 6.4187938 s

method {:test} Test4() {
var r0 := ToggleCase("a\U{001A}aa");
expect |r0| == |"a\U{001A}aa"|;
expect forall i :: 0 <= i < |"a\U{001A}aa"| ==> if IsLowerCase("a\U{001A}aa"[i]) then IsLowerUpperPair("a\U{001A}aa"[i], r0[i]) else if IsUpperCase("a\U{001A}aa"[i]) then IsUpperLowerPair("a\U{001A}aa"[i], r0[i]) else r0[i] == "a\U{001A}aa"[i];
}

// REPEAT 5 - TIME: 7.5794068 s

method {:test} Test5() {
var r0 := ToggleCase("0\U{000F}a a");
expect |r0| == |"0\U{000F}a a"|;
expect forall i :: 0 <= i < |"0\U{000F}a a"| ==> if IsLowerCase("0\U{000F}a a"[i]) then IsLowerUpperPair("0\U{000F}a a"[i], r0[i]) else if IsUpperCase("0\U{000F}a a"[i]) then IsUpperLowerPair("0\U{000F}a a"[i], r0[i]) else r0[i] == "0\U{000F}a a"[i];
}

// REPEAT 6 - TIME: 8.503135 s

method {:test} Test6() {
var r0 := ToggleCase("`{");
expect |r0| == |"`{"|;
expect forall i :: 0 <= i < |"`{"| ==> if IsLowerCase("`{"[i]) then IsLowerUpperPair("`{"[i], r0[i]) else if IsUpperCase("`{"[i]) then IsUpperLowerPair("`{"[i], r0[i]) else r0[i] == "`{"[i];
}

// REPEAT 7 - TIME: 9.319753 s

method {:test} Test7() {
var r0 := ToggleCase("2\U{0010}aaaaaaaa aaaaaaaaaaaaaaaa\U{000F}");
expect |r0| == |"2\U{0010}aaaaaaaa aaaaaaaaaaaaaaaa\U{000F}"|;
expect forall i :: 0 <= i < |"2\U{0010}aaaaaaaa aaaaaaaaaaaaaaaa\U{000F}"| ==> if IsLowerCase("2\U{0010}aaaaaaaa aaaaaaaaaaaaaaaa\U{000F}"[i]) then IsLowerUpperPair("2\U{0010}aaaaaaaa aaaaaaaaaaaaaaaa\U{000F}"[i], r0[i]) else if IsUpperCase("2\U{0010}aaaaaaaa aaaaaaaaaaaaaaaa\U{000F}"[i]) then IsUpperLowerPair("2\U{0010}aaaaaaaa aaaaaaaaaaaaaaaa\U{000F}"[i], r0[i]) else r0[i] == "2\U{0010}aaaaaaaa aaaaaaaaaaaaaaaa\U{000F}"[i];
}

// REPEAT 8 - TIME: 10.2476236 s

method {:test} Test8() {
var r0 := ToggleCase(" \U{001A}aa");
expect |r0| == |" \U{001A}aa"|;
expect forall i :: 0 <= i < |" \U{001A}aa"| ==> if IsLowerCase(" \U{001A}aa"[i]) then IsLowerUpperPair(" \U{001A}aa"[i], r0[i]) else if IsUpperCase(" \U{001A}aa"[i]) then IsUpperLowerPair(" \U{001A}aa"[i], r0[i]) else r0[i] == " \U{001A}aa"[i];
}

// REPEAT 9 - TIME: 11.1758665 s

method {:test} Test9() {
var r0 := ToggleCase("\U{000F}\U{000F}a");
expect |r0| == |"\U{000F}\U{000F}a"|;
expect forall i :: 0 <= i < |"\U{000F}\U{000F}a"| ==> if IsLowerCase("\U{000F}\U{000F}a"[i]) then IsLowerUpperPair("\U{000F}\U{000F}a"[i], r0[i]) else if IsUpperCase("\U{000F}\U{000F}a"[i]) then IsUpperLowerPair("\U{000F}\U{000F}a"[i], r0[i]) else r0[i] == "\U{000F}\U{000F}a"[i];
}

// REPEAT 10 - TIME: 11.9394881 s

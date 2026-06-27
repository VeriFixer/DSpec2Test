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
    if IsLowerCase(s[i]) {
      s' := s' + [ShiftMinus32(s[i])];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test6() {
var r0 := ToggleCase("aa@");
expect |r0| == |"aa@"|;
expect forall i :: 0 <= i < |"aa@"| ==> if IsLowerCase("aa@"[i]) then IsLowerUpperPair("aa@"[i], r0[i]) else if IsUpperCase("aa@"[i]) then IsUpperLowerPair("aa@"[i], r0[i]) else r0[i] == "aa@"[i];
}
method {:test} Test7() {
var r0 := ToggleCase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test8() {
var r0 := ToggleCase("afc");
expect |r0| == |"afc"|;
expect forall i :: 0 <= i < |"afc"| ==> if IsLowerCase("afc"[i]) then IsLowerUpperPair("afc"[i], r0[i]) else if IsUpperCase("afc"[i]) then IsUpperLowerPair("afc"[i], r0[i]) else r0[i] == "afc"[i];
}
method {:test} Test9() {
var r0 := ToggleCase("a\U{000F} ");
expect |r0| == |"a\U{000F} "|;
expect forall i :: 0 <= i < |"a\U{000F} "| ==> if IsLowerCase("a\U{000F} "[i]) then IsLowerUpperPair("a\U{000F} "[i], r0[i]) else if IsUpperCase("a\U{000F} "[i]) then IsUpperLowerPair("a\U{000F} "[i], r0[i]) else r0[i] == "a\U{000F} "[i];
}
method {:test} Test10() {
var r0 := ToggleCase("k");
expect |r0| == |"k"|;
expect forall i :: 0 <= i < |"k"| ==> if IsLowerCase("k"[i]) then IsLowerUpperPair("k"[i], r0[i]) else if IsUpperCase("k"[i]) then IsUpperLowerPair("k"[i], r0[i]) else r0[i] == "k"[i];
}
method {:test} Test11() {
var r0 := ToggleCase("C{");
expect |r0| == |"C{"|;
expect forall i :: 0 <= i < |"C{"| ==> if IsLowerCase("C{"[i]) then IsLowerUpperPair("C{"[i], r0[i]) else if IsUpperCase("C{"[i]) then IsUpperLowerPair("C{"[i], r0[i]) else r0[i] == "C{"[i];
}

// REPEAT 2 - TIME: 9.5108206 s

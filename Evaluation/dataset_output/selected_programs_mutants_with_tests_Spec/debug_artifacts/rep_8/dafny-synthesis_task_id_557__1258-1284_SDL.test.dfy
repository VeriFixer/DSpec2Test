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
    } else if IsUpperCase(s[i]) {
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test7() {
var r0 := ToggleCase("d\U{001B}aa");
expect |r0| == |"d\U{001B}aa"|;
expect forall i :: 0 <= i < |"d\U{001B}aa"| ==> if IsLowerCase("d\U{001B}aa"[i]) then IsLowerUpperPair("d\U{001B}aa"[i], r0[i]) else if IsUpperCase("d\U{001B}aa"[i]) then IsUpperLowerPair("d\U{001B}aa"[i], r0[i]) else r0[i] == "d\U{001B}aa"[i];
}

// REPEAT 8 - TIME: 10.619115 s

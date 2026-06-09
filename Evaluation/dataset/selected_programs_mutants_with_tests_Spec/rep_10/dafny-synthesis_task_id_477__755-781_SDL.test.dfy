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
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test9() {
var r0 := ToLowercase("a\U{0010}aa  ");
expect |r0| == |"a\U{0010}aa  "|;
expect forall i :: 0 <= i < |"a\U{0010}aa  "| ==> if IsUpperCase("a\U{0010}aa  "[i]) then IsUpperLowerPair("a\U{0010}aa  "[i], r0[i]) else r0[i] == "a\U{0010}aa  "[i];
}

// REPEAT 10 - TIME: 10.7557904 s

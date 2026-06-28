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
var r0 := ToLowercase("C");
expect |r0| == |"C"|;
expect forall i :: 0 <= i < |"C"| ==> if IsUpperCase("C"[i]) then IsUpperLowerPair("C"[i], r0[i]) else r0[i] == "C"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("Ya");
expect |r0| == |"Ya"|;
expect forall i :: 0 <= i < |"Ya"| ==> if IsUpperCase("Ya"[i]) then IsUpperLowerPair("Ya"[i], r0[i]) else r0[i] == "Ya"[i];
}
method {:test} Test6() {
var r0 := ToLowercase("[aaaaaaaaaaaaaaaaa.");
expect |r0| == |"[aaaaaaaaaaaaaaaaa."|;
expect forall i :: 0 <= i < |"[aaaaaaaaaaaaaaaaa."| ==> if IsUpperCase("[aaaaaaaaaaaaaaaaa."[i]) then IsUpperLowerPair("[aaaaaaaaaaaaaaaaa."[i], r0[i]) else r0[i] == "[aaaaaaaaaaaaaaaaa."[i];
}
method {:test} Test7() {
var r0 := ToLowercase("[");
expect |r0| == |"["|;
expect forall i :: 0 <= i < |"["| ==> if IsUpperCase("["[i]) then IsUpperLowerPair("["[i], r0[i]) else r0[i] == "["[i];
}

// REPEAT 2 - TIME: 7.7445525 s

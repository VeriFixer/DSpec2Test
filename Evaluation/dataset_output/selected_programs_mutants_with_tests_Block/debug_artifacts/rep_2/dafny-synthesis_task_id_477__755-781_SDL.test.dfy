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

method {:test} Test4() {
var r0 := ToLowercase("M");
expect |r0| == |"M"|;
expect forall i :: 0 <= i < |"M"| ==> if IsUpperCase("M"[i]) then IsUpperLowerPair("M"[i], r0[i]) else r0[i] == "M"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("[");
expect |r0| == |"["|;
expect forall i :: 0 <= i < |"["| ==> if IsUpperCase("["[i]) then IsUpperLowerPair("["[i], r0[i]) else r0[i] == "["[i];
}
method {:test} Test6() {
var r0 := ToLowercase("\U{0015}aaaaaaaaaaaaaa%");
expect |r0| == |"\U{0015}aaaaaaaaaaaaaa%"|;
expect forall i :: 0 <= i < |"\U{0015}aaaaaaaaaaaaaa%"| ==> if IsUpperCase("\U{0015}aaaaaaaaaaaaaa%"[i]) then IsUpperLowerPair("\U{0015}aaaaaaaaaaaaaa%"[i], r0[i]) else r0[i] == "\U{0015}aaaaaaaaaaaaaa%"[i];
}
method {:test} Test7() {
var r0 := ToLowercase("\U{001A}CD");
expect |r0| == |"\U{001A}CD"|;
expect forall i :: 0 <= i < |"\U{001A}CD"| ==> if IsUpperCase("\U{001A}CD"[i]) then IsUpperLowerPair("\U{001A}CD"[i], r0[i]) else r0[i] == "\U{001A}CD"[i];
}

// REPEAT 2 - TIME: 6.7057779 s

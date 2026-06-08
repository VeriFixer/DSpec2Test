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

method {:test} Test15() {
var r0 := ToLowercase("-\U{0010}aaaa\U{000F}a  ");
expect |r0| == |"-\U{0010}aaaa\U{000F}a  "|;
expect forall i :: 0 <= i < |"-\U{0010}aaaa\U{000F}a  "| ==> if IsUpperCase("-\U{0010}aaaa\U{000F}a  "[i]) then IsUpperLowerPair("-\U{0010}aaaa\U{000F}a  "[i], r0[i]) else r0[i] == "-\U{0010}aaaa\U{000F}a  "[i];
}

// REPEAT 7 - TIME: 12.8318222 s

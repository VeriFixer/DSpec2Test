// dafny-synthesis_task_id_732.dfy

predicate IsSpaceCommaDot(c: char)
{
  c == ' ' || c == ',' || c == '.'
}

method {:testEntry} ReplaceWithColon(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> s'[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> s'[k] == s[k])
  {
    s' := s' + [s[i]];
  }
  return s';
}

method {:test} Test4() {
var r0 := ReplaceWithColon("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> (IsSpaceCommaDot("\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0"[i]) ==> r0[i] == "\0"[i]);
}
method {:test} Test7() {
var r0 := ReplaceWithColon("a\0\U{0002}");
expect |r0| == |"a\0\U{0002}"|;
expect forall i :: 0 <= i < |"a\0\U{0002}"| ==> (IsSpaceCommaDot("a\0\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0\U{0002}"[i]) ==> r0[i] == "a\0\U{0002}"[i]);
}

// REPEAT 2 - TIME: 6.1187073 s

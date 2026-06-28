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
var r0 := ReplaceWithColon(":");
expect |r0| == |":"|;
expect forall i :: 0 <= i < |":"| ==> (IsSpaceCommaDot(":"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":"[i]) ==> r0[i] == ":"[i]);
}
method {:test} Test5() {
var r0 := ReplaceWithColon("a  ");
expect |r0| == |"a  "|;
expect forall i :: 0 <= i < |"a  "| ==> (IsSpaceCommaDot("a  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a  "[i]) ==> r0[i] == "a  "[i]);
}
method {:test} Test6() {
var r0 := ReplaceWithColon("a  aaaaaaa");
expect |r0| == |"a  aaaaaaa"|;
expect forall i :: 0 <= i < |"a  aaaaaaa"| ==> (IsSpaceCommaDot("a  aaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a  aaaaaaa"[i]) ==> r0[i] == "a  aaaaaaa"[i]);
}
method {:test} Test7() {
var r0 := ReplaceWithColon("\U{0001}aaaaaaaaa\0");
expect |r0| == |"\U{0001}aaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaa\0"| ==> (IsSpaceCommaDot("\U{0001}aaaaaaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0001}aaaaaaaaa\0"[i]) ==> r0[i] == "\U{0001}aaaaaaaaa\0"[i]);
}

// REPEAT 2 - TIME: 6.658762 s

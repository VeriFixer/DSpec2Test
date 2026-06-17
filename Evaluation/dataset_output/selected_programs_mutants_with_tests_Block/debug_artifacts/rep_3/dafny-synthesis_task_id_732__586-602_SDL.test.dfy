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
    if IsSpaceCommaDot(s[i]) {
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}

method {:test} Test8() {
var r0 := ReplaceWithColon(":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| == |":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> (IsSpaceCommaDot(":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]) ==> r0[i] == ":aa aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]);
}
method {:test} Test9() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i]);
}
method {:test} Test10() {
var r0 := ReplaceWithColon("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceWithColon("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "a\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 8.6178808 s

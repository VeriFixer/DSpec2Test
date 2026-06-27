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


method {:test} Test0() {
var r0 := ReplaceWithColon("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> (IsSpaceCommaDot("a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a"[i]) ==> r0[i] == "a"[i]);
}

// REPEAT 1 - TIME: 3.2814791 s

method {:test} Test1() {
var r0 := ReplaceWithColon("a\0");
expect |r0| == |"a\0"|;
expect forall i :: 0 <= i < |"a\0"| ==> (IsSpaceCommaDot("a\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0"[i]) ==> r0[i] == "a\0"[i]);
}

// REPEAT 2 - TIME: 4.4904186 s

method {:test} Test2() {
var r0 := ReplaceWithColon("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (IsSpaceCommaDot(""[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(""[i]) ==> r0[i] == ""[i]);
}

// REPEAT 3 - TIME: 5.6374055 s

method {:test} Test3() {
var r0 := ReplaceWithColon("a aaaaaaaaaa\0");
expect |r0| == |"a aaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"a aaaaaaaaaa\0"| ==> (IsSpaceCommaDot("a aaaaaaaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a aaaaaaaaaa\0"[i]) ==> r0[i] == "a aaaaaaaaaa\0"[i]);
}

// REPEAT 4 - TIME: 6.6708449 s

method {:test} Test4() {
var r0 := ReplaceWithColon("::");
expect |r0| == |"::"|;
expect forall i :: 0 <= i < |"::"| ==> (IsSpaceCommaDot("::"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("::"[i]) ==> r0[i] == "::"[i]);
}

// REPEAT 5 - TIME: 7.6590922 s

method {:test} Test5() {
var r0 := ReplaceWithColon(" aa");
expect |r0| == |" aa"|;
expect forall i :: 0 <= i < |" aa"| ==> (IsSpaceCommaDot(" aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aa"[i]) ==> r0[i] == " aa"[i]);
}

// REPEAT 6 - TIME: 8.6053403 s

method {:test} Test6() {
var r0 := ReplaceWithColon(",  ");
expect |r0| == |",  "|;
expect forall i :: 0 <= i < |",  "| ==> (IsSpaceCommaDot(",  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",  "[i]) ==> r0[i] == ",  "[i]);
}

// REPEAT 7 - TIME: 9.5282174 s

method {:test} Test7() {
var r0 := ReplaceWithColon("  aaaaaa aa a ");
expect |r0| == |"  aaaaaa aa a "|;
expect forall i :: 0 <= i < |"  aaaaaa aa a "| ==> (IsSpaceCommaDot("  aaaaaa aa a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  aaaaaa aa a "[i]) ==> r0[i] == "  aaaaaa aa a "[i]);
}

// REPEAT 8 - TIME: 10.3240225 s

method {:test} Test8() {
var r0 := ReplaceWithColon("    aaaaaa ");
expect |r0| == |"    aaaaaa "|;
expect forall i :: 0 <= i < |"    aaaaaa "| ==> (IsSpaceCommaDot("    aaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("    aaaaaa "[i]) ==> r0[i] == "    aaaaaa "[i]);
}

// REPEAT 9 - TIME: 11.2082996 s

method {:test} Test9() {
var r0 := ReplaceWithColon("\U{0001}\0aaaaaaaaaa");
expect |r0| == |"\U{0001}\0aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}\0aaaaaaaaaa"| ==> (IsSpaceCommaDot("\U{0001}\0aaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0001}\0aaaaaaaaaa"[i]) ==> r0[i] == "\U{0001}\0aaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 11.9497115 s

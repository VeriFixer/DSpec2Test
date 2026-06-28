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
      s' := s' + [':'];
    } else {
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ReplaceWithColon("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> (IsSpaceCommaDot("a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a"[i]) ==> r0[i] == "a"[i]);
}

// REPEAT 1 - TIME: 3.1851408 s

method {:test} Test1() {
var r0 := ReplaceWithColon("a:");
expect |r0| == |"a:"|;
expect forall i :: 0 <= i < |"a:"| ==> (IsSpaceCommaDot("a:"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a:"[i]) ==> r0[i] == "a:"[i]);
}

// REPEAT 2 - TIME: 4.1270806 s

method {:test} Test2() {
var r0 := ReplaceWithColon("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (IsSpaceCommaDot(""[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(""[i]) ==> r0[i] == ""[i]);
}

// REPEAT 3 - TIME: 5.3832287 s

method {:test} Test3() {
var r0 := ReplaceWithColon("\U{0001}\0");
expect |r0| == |"\U{0001}\0"|;
expect forall i :: 0 <= i < |"\U{0001}\0"| ==> (IsSpaceCommaDot("\U{0001}\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0001}\0"[i]) ==> r0[i] == "\U{0001}\0"[i]);
}

// REPEAT 4 - TIME: 6.5049285 s

method {:test} Test4() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaa\0a");
expect |r0| == |"aaaaaaaaaaaaaaaaaa\0a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaa\0a"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaa\0a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaa\0a"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaa\0a"[i]);
}

// REPEAT 5 - TIME: 7.6125906 s

method {:test} Test5() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaa ");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa "| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaa "[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 6 - TIME: 8.7619084 s

method {:test} Test6() {
var r0 := ReplaceWithColon(" a aaaaaaaaaaaaaaaaa ");
expect |r0| == |" a aaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |" a aaaaaaaaaaaaaaaaa "| ==> (IsSpaceCommaDot(" a aaaaaaaaaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a aaaaaaaaaaaaaaaaa "[i]) ==> r0[i] == " a aaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 7 - TIME: 9.6243671 s

method {:test} Test7() {
var r0 := ReplaceWithColon("\U{0002}aa\0aa\U{0001}");
expect |r0| == |"\U{0002}aa\0aa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0002}aa\0aa\U{0001}"| ==> (IsSpaceCommaDot("\U{0002}aa\0aa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0002}aa\0aa\U{0001}"[i]) ==> r0[i] == "\U{0002}aa\0aa\U{0001}"[i]);
}

// REPEAT 8 - TIME: 10.340112 s

method {:test} Test8() {
var r0 := ReplaceWithColon("  aa aa aaaaaaaaaaaa  ");
expect |r0| == |"  aa aa aaaaaaaaaaaa  "|;
expect forall i :: 0 <= i < |"  aa aa aaaaaaaaaaaa  "| ==> (IsSpaceCommaDot("  aa aa aaaaaaaaaaaa  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  aa aa aaaaaaaaaaaa  "[i]) ==> r0[i] == "  aa aa aaaaaaaaaaaa  "[i]);
}

// REPEAT 9 - TIME: 11.2165232 s

method {:test} Test9() {
var r0 := ReplaceWithColon("   a");
expect |r0| == |"   a"|;
expect forall i :: 0 <= i < |"   a"| ==> (IsSpaceCommaDot("   a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("   a"[i]) ==> r0[i] == "   a"[i]);
}

// REPEAT 10 - TIME: 11.922731 s

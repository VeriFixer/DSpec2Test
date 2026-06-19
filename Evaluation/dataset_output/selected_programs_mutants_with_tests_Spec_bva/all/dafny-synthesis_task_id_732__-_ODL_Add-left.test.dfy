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
      s' := [':'];
    } else {
      s' := [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ReplaceWithColon("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> (IsSpaceCommaDot("a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a"[i]) ==> r0[i] == "a"[i]);
}
method {:test} Test1() {
var r0 := ReplaceWithColon("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (IsSpaceCommaDot(""[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(""[i]) ==> r0[i] == ""[i]);
}
method {:test} Test3() {
var r0 := ReplaceWithColon("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> (IsSpaceCommaDot("aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa"[i]) ==> r0[i] == "aa"[i]);
}

// REPEAT 1 - TIME: 6.7209964 s

method {:test} Test10() {
var r0 := ReplaceWithColon("a\0aaaaaaaaaa\U{0001}");
expect |r0| == |"a\0aaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("a\0aaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0aaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "a\0aaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 7.4352309 s

method {:test} Test11() {
var r0 := ReplaceWithColon("\0a aaaaaaaaaaa\U{0001}");
expect |r0| == |"\0a aaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\0a aaaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("\0a aaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0a aaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "\0a aaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 8.1698093 s

method {:test} Test12() {
var r0 := ReplaceWithColon("a aaaaaaaaaaa ");
expect |r0| == |"a aaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"a aaaaaaaaaaa "| ==> (IsSpaceCommaDot("a aaaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a aaaaaaaaaaa "[i]) ==> r0[i] == "a aaaaaaaaaaa "[i]);
}

// REPEAT 4 - TIME: 8.9496864 s

method {:test} Test13() {
var r0 := ReplaceWithColon(" a aaaaaaa ");
expect |r0| == |" a aaaaaaa "|;
expect forall i :: 0 <= i < |" a aaaaaaa "| ==> (IsSpaceCommaDot(" a aaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a aaaaaaa "[i]) ==> r0[i] == " a aaaaaaa "[i]);
}

// REPEAT 5 - TIME: 9.602617 s

method {:test} Test14() {
var r0 := ReplaceWithColon(",aaaaaa aaaaaaaa");
expect |r0| == |",aaaaaa aaaaaaaa"|;
expect forall i :: 0 <= i < |",aaaaaa aaaaaaaa"| ==> (IsSpaceCommaDot(",aaaaaa aaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",aaaaaa aaaaaaaa"[i]) ==> r0[i] == ",aaaaaa aaaaaaaa"[i]);
}

// REPEAT 6 - TIME: 10.3594169 s

method {:test} Test15() {
var r0 := ReplaceWithColon(", aaaaaaaaaaaa ");
expect |r0| == |", aaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |", aaaaaaaaaaaa "| ==> (IsSpaceCommaDot(", aaaaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(", aaaaaaaaaaaa "[i]) ==> r0[i] == ", aaaaaaaaaaaa "[i]);
}

// REPEAT 7 - TIME: 11.0258746 s

method {:test} Test16() {
var r0 := ReplaceWithColon("\U{0001}a\0");
expect |r0| == |"\U{0001}a\0"|;
expect forall i :: 0 <= i < |"\U{0001}a\0"| ==> (IsSpaceCommaDot("\U{0001}a\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0001}a\0"[i]) ==> r0[i] == "\U{0001}a\0"[i]);
}

// REPEAT 8 - TIME: 11.76153 s

method {:test} Test17() {
var r0 := ReplaceWithColon("  a ");
expect |r0| == |"  a "|;
expect forall i :: 0 <= i < |"  a "| ==> (IsSpaceCommaDot("  a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  a "[i]) ==> r0[i] == "  a "[i]);
}

// REPEAT 9 - TIME: 12.3637305 s

method {:test} Test18() {
var r0 := ReplaceWithColon(" aaa a aa a ");
expect |r0| == |" aaa a aa a "|;
expect forall i :: 0 <= i < |" aaa a aa a "| ==> (IsSpaceCommaDot(" aaa a aa a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaa a aa a "[i]) ==> r0[i] == " aaa a aa a "[i]);
}

// REPEAT 10 - TIME: 13.010106 s

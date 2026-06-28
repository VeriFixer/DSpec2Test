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

// REPEAT 1 - TIME: 9.2137806 s

method {:test} Test10() {
var r0 := ReplaceWithColon("a:aaaaaaaaaa\0");
expect |r0| == |"a:aaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"a:aaaaaaaaaa\0"| ==> (IsSpaceCommaDot("a:aaaaaaaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a:aaaaaaaaaa\0"[i]) ==> r0[i] == "a:aaaaaaaaaa\0"[i]);
}

// REPEAT 2 - TIME: 10.2944372 s

method {:test} Test11() {
var r0 := ReplaceWithColon(":a");
expect |r0| == |":a"|;
expect forall i :: 0 <= i < |":a"| ==> (IsSpaceCommaDot(":a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":a"[i]) ==> r0[i] == ":a"[i]);
}

// REPEAT 3 - TIME: 11.2420135 s

method {:test} Test12() {
var r0 := ReplaceWithColon(" a ");
expect |r0| == |" a "|;
expect forall i :: 0 <= i < |" a "| ==> (IsSpaceCommaDot(" a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a "[i]) ==> r0[i] == " a "[i]);
}

// REPEAT 4 - TIME: 12.2238955 s

method {:test} Test13() {
var r0 := ReplaceWithColon("  ");
expect |r0| == |"  "|;
expect forall i :: 0 <= i < |"  "| ==> (IsSpaceCommaDot("  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  "[i]) ==> r0[i] == "  "[i]);
}

// REPEAT 5 - TIME: 13.1061722 s

method {:test} Test14() {
var r0 := ReplaceWithColon(", aaaaaaaaaa ");
expect |r0| == |", aaaaaaaaaa "|;
expect forall i :: 0 <= i < |", aaaaaaaaaa "| ==> (IsSpaceCommaDot(", aaaaaaaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(", aaaaaaaaaa "[i]) ==> r0[i] == ", aaaaaaaaaa "[i]);
}

// REPEAT 6 - TIME: 13.9234068 s

method {:test} Test15() {
var r0 := ReplaceWithColon(",a");
expect |r0| == |",a"|;
expect forall i :: 0 <= i < |",a"| ==> (IsSpaceCommaDot(",a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",a"[i]) ==> r0[i] == ",a"[i]);
}

// REPEAT 7 - TIME: 14.7589673 s

method {:test} Test16() {
var r0 := ReplaceWithColon(". a a a");
expect |r0| == |". a a a"|;
expect forall i :: 0 <= i < |". a a a"| ==> (IsSpaceCommaDot(". a a a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(". a a a"[i]) ==> r0[i] == ". a a a"[i]);
}

// REPEAT 8 - TIME: 15.6122825 s

method {:test} Test17() {
var r0 := ReplaceWithColon("  aa");
expect |r0| == |"  aa"|;
expect forall i :: 0 <= i < |"  aa"| ==> (IsSpaceCommaDot("  aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  aa"[i]) ==> r0[i] == "  aa"[i]);
}

// REPEAT 9 - TIME: 16.4327742 s

method {:test} Test18() {
var r0 := ReplaceWithColon("  aaaaa ");
expect |r0| == |"  aaaaa "|;
expect forall i :: 0 <= i < |"  aaaaa "| ==> (IsSpaceCommaDot("  aaaaa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("  aaaaa "[i]) ==> r0[i] == "  aaaaa "[i]);
}

// REPEAT 10 - TIME: 17.1930407 s

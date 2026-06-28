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
method {:test} Test2() {
var r0 := ReplaceWithColon("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (IsSpaceCommaDot(""[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(""[i]) ==> r0[i] == ""[i]);
}
method {:test} Test3() {
var r0 := ReplaceWithColon("a\0");
expect |r0| == |"a\0"|;
expect forall i :: 0 <= i < |"a\0"| ==> (IsSpaceCommaDot("a\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0"[i]) ==> r0[i] == "a\0"[i]);
}

// REPEAT 1 - TIME: 4.1754359 s

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

method {:test} Test8() {
var r0 := ReplaceWithColon(" a ");
expect |r0| == |" a "|;
expect forall i :: 0 <= i < |" a "| ==> (IsSpaceCommaDot(" a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a "[i]) ==> r0[i] == " a "[i]);
}
method {:test} Test9() {
var r0 := ReplaceWithColon(" aa");
expect |r0| == |" aa"|;
expect forall i :: 0 <= i < |" aa"| ==> (IsSpaceCommaDot(" aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aa"[i]) ==> r0[i] == " aa"[i]);
}
method {:test} Test10() {
var r0 := ReplaceWithColon(":a");
expect |r0| == |":a"|;
expect forall i :: 0 <= i < |":a"| ==> (IsSpaceCommaDot(":a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":a"[i]) ==> r0[i] == ":a"[i]);
}
method {:test} Test11() {
var r0 := ReplaceWithColon("\U{0001}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0003}");
expect |r0| == |"\U{0001}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"\U{0001}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"| ==> (IsSpaceCommaDot("\U{0001}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0001}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]) ==> r0[i] == "\U{0001}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 3 - TIME: 9.0944257 s

method {:test} Test12() {
var r0 := ReplaceWithColon(" aa ");
expect |r0| == |" aa "|;
expect forall i :: 0 <= i < |" aa "| ==> (IsSpaceCommaDot(" aa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aa "[i]) ==> r0[i] == " aa "[i]);
}
method {:test} Test13() {
var r0 := ReplaceWithColon(" aaa a  a");
expect |r0| == |" aaa a  a"|;
expect forall i :: 0 <= i < |" aaa a  a"| ==> (IsSpaceCommaDot(" aaa a  a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaa a  a"[i]) ==> r0[i] == " aaa a  a"[i]);
}
method {:test} Test14() {
var r0 := ReplaceWithColon("    ");
expect |r0| == |"    "|;
expect forall i :: 0 <= i < |"    "| ==> (IsSpaceCommaDot("    "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("    "[i]) ==> r0[i] == "    "[i]);
}
method {:test} Test15() {
var r0 := ReplaceWithColon("\0aaaaaa\U{0001}aaaa\U{0002}aaaaaaaaaaaa\U{0003}");
expect |r0| == |"\0aaaaaa\U{0001}aaaa\U{0002}aaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"\0aaaaaa\U{0001}aaaa\U{0002}aaaaaaaaaaaa\U{0003}"| ==> (IsSpaceCommaDot("\0aaaaaa\U{0001}aaaa\U{0002}aaaaaaaaaaaa\U{0003}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaaa\U{0001}aaaa\U{0002}aaaaaaaaaaaa\U{0003}"[i]) ==> r0[i] == "\0aaaaaa\U{0001}aaaa\U{0002}aaaaaaaaaaaa\U{0003}"[i]);
}

// REPEAT 4 - TIME: 11.483122 s

method {:test} Test16() {
var r0 := ReplaceWithColon("aaaaaaa a  a");
expect |r0| == |"aaaaaaa a  a"|;
expect forall i :: 0 <= i < |"aaaaaaa a  a"| ==> (IsSpaceCommaDot("aaaaaaa a  a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaa a  a"[i]) ==> r0[i] == "aaaaaaa a  a"[i]);
}
method {:test} Test17() {
var r0 := ReplaceWithColon("aa aaaaaaaaaa");
expect |r0| == |"aa aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aa aaaaaaaaaa"| ==> (IsSpaceCommaDot("aa aaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa aaaaaaaaaa"[i]) ==> r0[i] == "aa aaaaaaaaaa"[i]);
}
method {:test} Test18() {
var r0 := ReplaceWithColon(": ");
expect |r0| == |": "|;
expect forall i :: 0 <= i < |": "| ==> (IsSpaceCommaDot(": "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(": "[i]) ==> r0[i] == ": "[i]);
}
method {:test} Test19() {
var r0 := ReplaceWithColon("\0aa\U{0001} aaaa\U{0002}a  aaaaaaaaaa a     ");
expect |r0| == |"\0aa\U{0001} aaaa\U{0002}a  aaaaaaaaaa a     "|;
expect forall i :: 0 <= i < |"\0aa\U{0001} aaaa\U{0002}a  aaaaaaaaaa a     "| ==> (IsSpaceCommaDot("\0aa\U{0001} aaaa\U{0002}a  aaaaaaaaaa a     "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa\U{0001} aaaa\U{0002}a  aaaaaaaaaa a     "[i]) ==> r0[i] == "\0aa\U{0001} aaaa\U{0002}a  aaaaaaaaaa a     "[i]);
}

// REPEAT 5 - TIME: 14.1405769 s

method {:test} Test20() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaa aaaaaaaaaa  a");
expect |r0| == |" aaaaaaaaaaaaaa aaaaaaaaaa  a"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaa aaaaaaaaaa  a"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaa aaaaaaaaaa  a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaa aaaaaaaaaa  a"[i]) ==> r0[i] == " aaaaaaaaaaaaaa aaaaaaaaaa  a"[i]);
}
method {:test} Test21() {
var r0 := ReplaceWithColon(",aaaaaaaaaaa");
expect |r0| == |",aaaaaaaaaaa"|;
expect forall i :: 0 <= i < |",aaaaaaaaaaa"| ==> (IsSpaceCommaDot(",aaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",aaaaaaaaaaa"[i]) ==> r0[i] == ",aaaaaaaaaaa"[i]);
}
method {:test} Test22() {
var r0 := ReplaceWithColon(":aa");
expect |r0| == |":aa"|;
expect forall i :: 0 <= i < |":aa"| ==> (IsSpaceCommaDot(":aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":aa"[i]) ==> r0[i] == ":aa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0001}");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0001}"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0001}"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0001}"[i]);
}

// REPEAT 6 - TIME: 16.1175378 s

method {:test} Test24() {
var r0 := ReplaceWithColon(" aaaa");
expect |r0| == |" aaaa"|;
expect forall i :: 0 <= i < |" aaaa"| ==> (IsSpaceCommaDot(" aaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaa"[i]) ==> r0[i] == " aaaa"[i]);
}
method {:test} Test25() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test27() {
var r0 := ReplaceWithColon("aa\0a aaaaaaaaaaaaaaaaaaaaa\U{0001}a");
expect |r0| == |"aa\0a aaaaaaaaaaaaaaaaaaaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aa\0a aaaaaaaaaaaaaaaaaaaaa\U{0001}a"| ==> (IsSpaceCommaDot("aa\0a aaaaaaaaaaaaaaaaaaaaa\U{0001}a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa\0a aaaaaaaaaaaaaaaaaaaaa\U{0001}a"[i]) ==> r0[i] == "aa\0a aaaaaaaaaaaaaaaaaaaaa\U{0001}a"[i]);
}

// REPEAT 7 - TIME: 18.1384229 s

method {:test} Test28() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaa  aaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaa  aaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaa  aaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaa  aaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaa  aaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaa  aaaaaaaaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceWithColon(",aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |",aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |",aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(",aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ",aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test30() {
var r0 := ReplaceWithColon(":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test31() {
var r0 := ReplaceWithColon("aaaaaaaaa\0aaa aaaa aaaaaa");
expect |r0| == |"aaaaaaaaa\0aaa aaaa aaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaa\0aaa aaaa aaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaa\0aaa aaaa aaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaa\0aaa aaaa aaaaaa"[i]) ==> r0[i] == "aaaaaaaaa\0aaa aaaa aaaaaa"[i]);
}

// REPEAT 8 - TIME: 20.4109281 s

method {:test} Test32() {
var r0 := ReplaceWithColon(". aaaaaaaaaaaaaaaaaaaaaaa a");
expect |r0| == |". aaaaaaaaaaaaaaaaaaaaaaa a"|;
expect forall i :: 0 <= i < |". aaaaaaaaaaaaaaaaaaaaaaa a"| ==> (IsSpaceCommaDot(". aaaaaaaaaaaaaaaaaaaaaaa a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(". aaaaaaaaaaaaaaaaaaaaaaa a"[i]) ==> r0[i] == ". aaaaaaaaaaaaaaaaaaaaaaa a"[i]);
}
method {:test} Test33() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaa"[i]);
}
method {:test} Test34() {
var r0 := ReplaceWithColon(".aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |".aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |".aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(".aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(".aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ".aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test35() {
var r0 := ReplaceWithColon("a\0aaaaaaaaaaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"a\0aaaaaaaaaaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaaaaaaaaaaaaa\U{0001}"| ==> (IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a\0aaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "a\0aaaaaaaaaaaaaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 9 - TIME: 23.5903459 s

method {:test} Test36() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaa"[i]);
}
method {:test} Test37() {
var r0 := ReplaceWithColon(": aaaaaa");
expect |r0| == |": aaaaaa"|;
expect forall i :: 0 <= i < |": aaaaaa"| ==> (IsSpaceCommaDot(": aaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(": aaaaaa"[i]) ==> r0[i] == ": aaaaaa"[i]);
}
method {:test} Test38() {
var r0 := ReplaceWithColon("aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test39() {
var r0 := ReplaceWithColon("\0aaaaaaaaaaaaaa");
expect |r0| == |"\0aaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0aaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0aaaaaaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 26.8530568 s

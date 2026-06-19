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
      s' := s';
    } else {
      s' := s';
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

// REPEAT 1 - TIME: 3.8395855 s

method {:test} Test4() {
var r0 := ReplaceWithColon("aaa");
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> (IsSpaceCommaDot("aaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa"[i]) ==> r0[i] == "aaa"[i]);
}
method {:test} Test5() {
var r0 := ReplaceWithColon(" ");
expect |r0| == |" "|;
expect forall i :: 0 <= i < |" "| ==> (IsSpaceCommaDot(" "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" "[i]) ==> r0[i] == " "[i]);
}
method {:test} Test7() {
var r0 := ReplaceWithColon(" aaaaa\0");
expect |r0| == |" aaaaa\0"|;
expect forall i :: 0 <= i < |" aaaaa\0"| ==> (IsSpaceCommaDot(" aaaaa\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaa\0"[i]) ==> r0[i] == " aaaaa\0"[i]);
}

// REPEAT 2 - TIME: 6.0656294 s

method {:test} Test8() {
var r0 := ReplaceWithColon("\0a\U{0001}\U{0002}");
expect |r0| == |"\0a\U{0001}\U{0002}"|;
expect forall i :: 0 <= i < |"\0a\U{0001}\U{0002}"| ==> (IsSpaceCommaDot("\0a\U{0001}\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0a\U{0001}\U{0002}"[i]) ==> r0[i] == "\0a\U{0001}\U{0002}"[i]);
}
method {:test} Test9() {
var r0 := ReplaceWithColon("\0  ");
expect |r0| == |"\0  "|;
expect forall i :: 0 <= i < |"\0  "| ==> (IsSpaceCommaDot("\0  "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0  "[i]) ==> r0[i] == "\0  "[i]);
}
method {:test} Test10() {
var r0 := ReplaceWithColon(",");
expect |r0| == |","|;
expect forall i :: 0 <= i < |","| ==> (IsSpaceCommaDot(","[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(","[i]) ==> r0[i] == ","[i]);
}
method {:test} Test11() {
var r0 := ReplaceWithColon("\U{0001}\0\U{0005}\U{0002}");
expect |r0| == |"\U{0001}\0\U{0005}\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0001}\0\U{0005}\U{0002}"| ==> (IsSpaceCommaDot("\U{0001}\0\U{0005}\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0001}\0\U{0005}\U{0002}"[i]) ==> r0[i] == "\U{0001}\0\U{0005}\U{0002}"[i]);
}

// REPEAT 3 - TIME: 8.5000027 s

method {:test} Test12() {
var r0 := ReplaceWithColon("\0aa\U{0001}\U{0002}");
expect |r0| == |"\0aa\U{0001}\U{0002}"|;
expect forall i :: 0 <= i < |"\0aa\U{0001}\U{0002}"| ==> (IsSpaceCommaDot("\0aa\U{0001}\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa\U{0001}\U{0002}"[i]) ==> r0[i] == "\0aa\U{0001}\U{0002}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceWithColon("aa aa");
expect |r0| == |"aa aa"|;
expect forall i :: 0 <= i < |"aa aa"| ==> (IsSpaceCommaDot("aa aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa aa"[i]) ==> r0[i] == "aa aa"[i]);
}
method {:test} Test14() {
var r0 := ReplaceWithColon(" aaaaa");
expect |r0| == |" aaaaa"|;
expect forall i :: 0 <= i < |" aaaaa"| ==> (IsSpaceCommaDot(" aaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaa"[i]) ==> r0[i] == " aaaaa"[i]);
}
method {:test} Test15() {
var r0 := ReplaceWithColon("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> (IsSpaceCommaDot("\0"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0"[i]) ==> r0[i] == "\0"[i]);
}

// REPEAT 4 - TIME: 10.7650042 s

method {:test} Test16() {
var r0 := ReplaceWithColon("\0aa\U{0001}aa\U{0003}aaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}");
expect |r0| == |"\0aa\U{0001}aa\U{0003}aaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}"|;
expect forall i :: 0 <= i < |"\0aa\U{0001}aa\U{0003}aaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}"| ==> (IsSpaceCommaDot("\0aa\U{0001}aa\U{0003}aaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa\U{0001}aa\U{0003}aaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}"[i]) ==> r0[i] == "\0aa\U{0001}aa\U{0003}aaaaaaaaaaaaaaaaaaa\U{0002}a\U{0004}"[i]);
}
method {:test} Test17() {
var r0 := ReplaceWithColon("\0 a ");
expect |r0| == |"\0 a "|;
expect forall i :: 0 <= i < |"\0 a "| ==> (IsSpaceCommaDot("\0 a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0 a "[i]) ==> r0[i] == "\0 a "[i]);
}
method {:test} Test18() {
var r0 := ReplaceWithColon(".");
expect |r0| == |"."|;
expect forall i :: 0 <= i < |"."| ==> (IsSpaceCommaDot("."[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("."[i]) ==> r0[i] == "."[i]);
}
method {:test} Test19() {
var r0 := ReplaceWithColon("\0aa\U{0002}\U{0004}aa\U{0001}");
expect |r0| == |"\0aa\U{0002}\U{0004}aa\U{0001}"|;
expect forall i :: 0 <= i < |"\0aa\U{0002}\U{0004}aa\U{0001}"| ==> (IsSpaceCommaDot("\0aa\U{0002}\U{0004}aa\U{0001}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa\U{0002}\U{0004}aa\U{0001}"[i]) ==> r0[i] == "\0aa\U{0002}\U{0004}aa\U{0001}"[i]);
}

// REPEAT 5 - TIME: 12.7386987 s

method {:test} Test20() {
var r0 := ReplaceWithColon("\0aa\U{0001}aaaa\U{0003}aaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}");
expect |r0| == |"\0aa\U{0001}aaaa\U{0003}aaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\0aa\U{0001}aaaa\U{0003}aaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}"| ==> (IsSpaceCommaDot("\0aa\U{0001}aaaa\U{0003}aaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa\U{0001}aaaa\U{0003}aaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}"[i]) ==> r0[i] == "\0aa\U{0001}aaaa\U{0003}aaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}"[i]);
}
method {:test} Test21() {
var r0 := ReplaceWithColon("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> (IsSpaceCommaDot("\0aa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aa"[i]) ==> r0[i] == "\0aa"[i]);
}
method {:test} Test22() {
var r0 := ReplaceWithColon("\0 a");
expect |r0| == |"\0 a"|;
expect forall i :: 0 <= i < |"\0 a"| ==> (IsSpaceCommaDot("\0 a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0 a"[i]) ==> r0[i] == "\0 a"[i]);
}
method {:test} Test23() {
var r0 := ReplaceWithColon("aa\0aaa\U{0001}\U{0002}\U{0003}");
expect |r0| == |"aa\0aaa\U{0001}\U{0002}\U{0003}"|;
expect forall i :: 0 <= i < |"aa\0aaa\U{0001}\U{0002}\U{0003}"| ==> (IsSpaceCommaDot("aa\0aaa\U{0001}\U{0002}\U{0003}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa\0aaa\U{0001}\U{0002}\U{0003}"[i]) ==> r0[i] == "aa\0aaa\U{0001}\U{0002}\U{0003}"[i]);
}

// REPEAT 6 - TIME: 14.4022434 s

method {:test} Test24() {
var r0 := ReplaceWithColon(" aa aaa   ");
expect |r0| == |" aa aaa   "|;
expect forall i :: 0 <= i < |" aa aaa   "| ==> (IsSpaceCommaDot(" aa aaa   "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aa aaa   "[i]) ==> r0[i] == " aa aaa   "[i]);
}
method {:test} Test25() {
var r0 := ReplaceWithColon(",aaaaa");
expect |r0| == |",aaaaa"|;
expect forall i :: 0 <= i < |",aaaaa"| ==> (IsSpaceCommaDot(",aaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",aaaaa"[i]) ==> r0[i] == ",aaaaa"[i]);
}
method {:test} Test26() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test27() {
var r0 := ReplaceWithColon("aa\0 aaaaa\U{0002}");
expect |r0| == |"aa\0 aaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"aa\0 aaaaa\U{0002}"| ==> (IsSpaceCommaDot("aa\0 aaaaa\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aa\0 aaaaa\U{0002}"[i]) ==> r0[i] == "aa\0 aaaaa\U{0002}"[i]);
}

// REPEAT 7 - TIME: 15.9375533 s

method {:test} Test28() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaa a  aaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaa a  aaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaa a  aaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaa a  aaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaa a  aaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaa a  aaaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceWithColon(",aaaaaaaa");
expect |r0| == |",aaaaaaaa"|;
expect forall i :: 0 <= i < |",aaaaaaaa"| ==> (IsSpaceCommaDot(",aaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",aaaaaaaa"[i]) ==> r0[i] == ",aaaaaaaa"[i]);
}
method {:test} Test30() {
var r0 := ReplaceWithColon("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test31() {
var r0 := ReplaceWithColon("aaa\0a\U{0002}\U{0003}aa\U{0001}aaaaaaa\U{0004}aaaaaaaaaa");
expect |r0| == |"aaa\0a\U{0002}\U{0003}aa\U{0001}aaaaaaa\U{0004}aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaa\0a\U{0002}\U{0003}aa\U{0001}aaaaaaa\U{0004}aaaaaaaaaa"| ==> (IsSpaceCommaDot("aaa\0a\U{0002}\U{0003}aa\U{0001}aaaaaaa\U{0004}aaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("aaa\0a\U{0002}\U{0003}aa\U{0001}aaaaaaa\U{0004}aaaaaaaaaa"[i]) ==> r0[i] == "aaa\0a\U{0002}\U{0003}aa\U{0001}aaaaaaa\U{0004}aaaaaaaaaa"[i]);
}

// REPEAT 8 - TIME: 18.0887514 s

method {:test} Test32() {
var r0 := ReplaceWithColon(" aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test33() {
var r0 := ReplaceWithColon(",\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |",\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |",\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(",\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ",\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test35() {
var r0 := ReplaceWithColon("\0aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 9 - TIME: 20.7372415 s

method {:test} Test36() {
var r0 := ReplaceWithColon("\U{0001}aaaaaaaaaaaaaaaaaaaaaaa\0a");
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaa\0a"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaaaaaa\0a"| ==> (IsSpaceCommaDot("\U{0001}aaaaaaaaaaaaaaaaaaaaaaa\0a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\U{0001}aaaaaaaaaaaaaaaaaaaaaaa\0a"[i]) ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaaaaaaaaa\0a"[i]);
}
method {:test} Test37() {
var r0 := ReplaceWithColon(": aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |": aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |": aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(": aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(": aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ": aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test38() {
var r0 := ReplaceWithColon(" \0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" \0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" \0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (IsSpaceCommaDot(" \0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" \0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == " \0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test39() {
var r0 := ReplaceWithColon("\0aaaaaaaaa\U{0002}");
expect |r0| == |"\0aaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaa\U{0002}"| ==> (IsSpaceCommaDot("\0aaaaaaaaa\U{0002}"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("\0aaaaaaaaa\U{0002}"[i]) ==> r0[i] == "\0aaaaaaaaa\U{0002}"[i]);
}

// REPEAT 10 - TIME: 23.2200484 s

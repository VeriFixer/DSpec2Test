// dafny-synthesis_task_id_732.dfy

predicate IsSpaceCommaDot(c: char)
{
  c == ' ' || c == ',' || c == '.'
}

method {:testEntry} ReplaceWithColon(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (IsSpaceCommaDot(s[i]) ==> v[i] == ':') && (!IsSpaceCommaDot(s[i]) ==> v[i] == s[i])
{
  var s': string := ['a', 'b', 'c'];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (IsSpaceCommaDot(s[k]) ==> s'[k] == ':') && (!IsSpaceCommaDot(s[k]) ==> s'[k] == s[k])
  {
    if IsSpaceCommaDot(s[i]) {
      s' := s' + [':'];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ReplaceWithColon("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> (IsSpaceCommaDot("a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("a"[i]) ==> r0[i] == "a"[i]);
}

// REPEAT 1 - TIME: 34.5690773 s

method {:test} Test1() {
var r0 := ReplaceWithColon(" ");
expect |r0| == |" "|;
expect forall i :: 0 <= i < |" "| ==> (IsSpaceCommaDot(" "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" "[i]) ==> r0[i] == " "[i]);
}

// REPEAT 2 - TIME: 65.6880364 s

method {:test} Test2() {
var r0 := ReplaceWithColon(":a");
expect |r0| == |":a"|;
expect forall i :: 0 <= i < |":a"| ==> (IsSpaceCommaDot(":a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(":a"[i]) ==> r0[i] == ":a"[i]);
}

// REPEAT 3 - TIME: 103.9152669 s

method {:test} Test3() {
var r0 := ReplaceWithColon("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (IsSpaceCommaDot(""[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(""[i]) ==> r0[i] == ""[i]);
}

// REPEAT 4 - TIME: 146.9405077 s

method {:test} Test4() {
var r0 := ReplaceWithColon(" a");
expect |r0| == |" a"|;
expect forall i :: 0 <= i < |" a"| ==> (IsSpaceCommaDot(" a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a"[i]) ==> r0[i] == " a"[i]);
}

// REPEAT 5 - TIME: 203.5802948 s

method {:test} Test5() {
var r0 := ReplaceWithColon(",");
expect |r0| == |","|;
expect forall i :: 0 <= i < |","| ==> (IsSpaceCommaDot(","[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(","[i]) ==> r0[i] == ","[i]);
}

// REPEAT 6 - TIME: 252.6444987 s

method {:test} Test6() {
var r0 := ReplaceWithColon(" a ");
expect |r0| == |" a "|;
expect forall i :: 0 <= i < |" a "| ==> (IsSpaceCommaDot(" a "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(" a "[i]) ==> r0[i] == " a "[i]);
}

// REPEAT 7 - TIME: 305.2429062 s

method {:test} Test7() {
var r0 := ReplaceWithColon(",aa ");
expect |r0| == |",aa "|;
expect forall i :: 0 <= i < |",aa "| ==> (IsSpaceCommaDot(",aa "[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(",aa "[i]) ==> r0[i] == ",aa "[i]);
}

// REPEAT 8 - TIME: 364.8045002 s

method {:test} Test8() {
var r0 := ReplaceWithColon(".");
expect |r0| == |"."|;
expect forall i :: 0 <= i < |"."| ==> (IsSpaceCommaDot("."[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot("."[i]) ==> r0[i] == "."[i]);
}

// REPEAT 9 - TIME: 421.4944215 s

method {:test} Test9() {
var r0 := ReplaceWithColon(", a");
expect |r0| == |", a"|;
expect forall i :: 0 <= i < |", a"| ==> (IsSpaceCommaDot(", a"[i]) ==> r0[i] == ':') && (!IsSpaceCommaDot(", a"[i]) ==> r0[i] == ", a"[i]);
}

// REPEAT 10 - TIME: 485.5315107 s

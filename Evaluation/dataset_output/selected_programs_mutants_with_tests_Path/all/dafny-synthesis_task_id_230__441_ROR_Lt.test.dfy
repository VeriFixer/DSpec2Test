// dafny-synthesis_task_id_230.dfy

method {:testEntry} ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> s'[k] == ch) && (s[k] != ' ' ==> s'[k] == s[k])
  {
    if s[i] < ' ' {
      s' := s' + [ch];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ReplaceBlanksWithChar("a", '\0');
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> ("a"[i] == ' ' ==> r0[i] == '\0') && ("a"[i] != ' ' ==> r0[i] == "a"[i]);
}

// REPEAT 1 - TIME: 33.9091337 s

method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("", '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == ' ' ==> r0[i] == '\0') && (""[i] != ' ' ==> r0[i] == ""[i]);
}

// REPEAT 2 - TIME: 67.9116138 s

method {:test} Test2() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}

// REPEAT 3 - TIME: 104.0539089 s

method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("aa", '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == ' ' ==> r0[i] == '\0') && ("aa"[i] != ' ' ==> r0[i] == "aa"[i]);
}

// REPEAT 4 - TIME: 163.8628424 s

method {:test} Test4() {
var r0 := ReplaceBlanksWithChar(" ", '\0');
expect |r0| == |" "|;
expect forall i :: 0 <= i < |" "| ==> (" "[i] == ' ' ==> r0[i] == '\0') && (" "[i] != ' ' ==> r0[i] == " "[i]);
}

// REPEAT 5 - TIME: 244.4496446 s

method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("aaa", '\0');
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> ("aaa"[i] == ' ' ==> r0[i] == '\0') && ("aaa"[i] != ' ' ==> r0[i] == "aaa"[i]);
}

// REPEAT 6 - TIME: 348.6514025 s

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar(" aaa", '\0');
expect |r0| == |" aaa"|;
expect forall i :: 0 <= i < |" aaa"| ==> (" aaa"[i] == ' ' ==> r0[i] == '\0') && (" aaa"[i] != ' ' ==> r0[i] == " aaa"[i]);
}

// REPEAT 7 - TIME: 447.9318039 s

method {:test} Test7() {
var r0 := ReplaceBlanksWithChar(" a aa", '\0');
expect |r0| == |" a aa"|;
expect forall i :: 0 <= i < |" a aa"| ==> (" a aa"[i] == ' ' ==> r0[i] == '\0') && (" a aa"[i] != ' ' ==> r0[i] == " a aa"[i]);
}

// REPEAT 8 - TIME: 547.1409458 s

method {:test} Test8() {
var r0 := ReplaceBlanksWithChar("  aaa ", '\0');
expect |r0| == |"  aaa "|;
expect forall i :: 0 <= i < |"  aaa "| ==> ("  aaa "[i] == ' ' ==> r0[i] == '\0') && ("  aaa "[i] != ' ' ==> r0[i] == "  aaa "[i]);
}

// REPEAT 9 - TIME: 635.8243665 s

method {:test} Test9() {
var r0 := ReplaceBlanksWithChar(" \U{0001} ", '\0');
expect |r0| == |" \U{0001} "|;
expect forall i :: 0 <= i < |" \U{0001} "| ==> (" \U{0001} "[i] == ' ' ==> r0[i] == '\0') && (" \U{0001} "[i] != ' ' ==> r0[i] == " \U{0001} "[i]);
}

// REPEAT 10 - TIME: 730.7903408 s

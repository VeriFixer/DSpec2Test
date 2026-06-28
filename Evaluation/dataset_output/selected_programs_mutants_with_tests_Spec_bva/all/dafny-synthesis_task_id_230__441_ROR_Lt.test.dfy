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
method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("", '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == ' ' ==> r0[i] == '\0') && (""[i] != ' ' ==> r0[i] == ""[i]);
}
method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("aa", '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == ' ' ==> r0[i] == '\0') && ("aa"[i] != ' ' ==> r0[i] == "aa"[i]);
}

// REPEAT 1 - TIME: 8.5990254 s

method {:test} Test10() {
var r0 := ReplaceBlanksWithChar("aaa", '\0');
expect |r0| == |"aaa"|;
expect forall i :: 0 <= i < |"aaa"| ==> ("aaa"[i] == ' ' ==> r0[i] == '\0') && ("aaa"[i] != ' ' ==> r0[i] == "aaa"[i]);
}

// REPEAT 2 - TIME: 9.7790648 s

method {:test} Test11() {
var r0 := ReplaceBlanksWithChar("\0 aaaaaaaaaaaa ", '\0');
expect |r0| == |"\0 aaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"\0 aaaaaaaaaaaa "| ==> ("\0 aaaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("\0 aaaaaaaaaaaa "[i] != ' ' ==> r0[i] == "\0 aaaaaaaaaaaa "[i]);
}

// REPEAT 3 - TIME: 10.8307415 s

method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("  a", '\0');
expect |r0| == |"  a"|;
expect forall i :: 0 <= i < |"  a"| ==> ("  a"[i] == ' ' ==> r0[i] == '\0') && ("  a"[i] != ' ' ==> r0[i] == "  a"[i]);
}

// REPEAT 4 - TIME: 11.9912908 s

method {:test} Test13() {
var r0 := ReplaceBlanksWithChar(" aaa", '\0');
expect |r0| == |" aaa"|;
expect forall i :: 0 <= i < |" aaa"| ==> (" aaa"[i] == ' ' ==> r0[i] == '\0') && (" aaa"[i] != ' ' ==> r0[i] == " aaa"[i]);
}

// REPEAT 5 - TIME: 12.8181271 s

method {:test} Test14() {
var r0 := ReplaceBlanksWithChar("a\U{0001}\U{0003}\U{0005}a", '\0');
expect |r0| == |"a\U{0001}\U{0003}\U{0005}a"|;
expect forall i :: 0 <= i < |"a\U{0001}\U{0003}\U{0005}a"| ==> ("a\U{0001}\U{0003}\U{0005}a"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}\U{0003}\U{0005}a"[i] != ' ' ==> r0[i] == "a\U{0001}\U{0003}\U{0005}a"[i]);
}

// REPEAT 6 - TIME: 13.7920874 s

method {:test} Test15() {
var r0 := ReplaceBlanksWithChar(" aaaaa", '\0');
expect |r0| == |" aaaaa"|;
expect forall i :: 0 <= i < |" aaaaa"| ==> (" aaaaa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaa"[i] != ' ' ==> r0[i] == " aaaaa"[i]);
}

// REPEAT 7 - TIME: 14.6870812 s

method {:test} Test16() {
var r0 := ReplaceBlanksWithChar("  aa", '\0');
expect |r0| == |"  aa"|;
expect forall i :: 0 <= i < |"  aa"| ==> ("  aa"[i] == ' ' ==> r0[i] == '\0') && ("  aa"[i] != ' ' ==> r0[i] == "  aa"[i]);
}

// REPEAT 8 - TIME: 15.4468298 s

method {:test} Test17() {
var r0 := ReplaceBlanksWithChar("\U{0003}aaa\U{0001}aaaaaaaaaaa", '\0');
expect |r0| == |"\U{0003}aaa\U{0001}aaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0003}aaa\U{0001}aaaaaaaaaaa"| ==> ("\U{0003}aaa\U{0001}aaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}aaa\U{0001}aaaaaaaaaaa"[i] != ' ' ==> r0[i] == "\U{0003}aaa\U{0001}aaaaaaaaaaa"[i]);
}

// REPEAT 9 - TIME: 16.265435 s

method {:test} Test18() {
var r0 := ReplaceBlanksWithChar("\U{0001}   a", '\0');
expect |r0| == |"\U{0001}   a"|;
expect forall i :: 0 <= i < |"\U{0001}   a"| ==> ("\U{0001}   a"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}   a"[i] != ' ' ==> r0[i] == "\U{0001}   a"[i]);
}

// REPEAT 10 - TIME: 17.1884972 s

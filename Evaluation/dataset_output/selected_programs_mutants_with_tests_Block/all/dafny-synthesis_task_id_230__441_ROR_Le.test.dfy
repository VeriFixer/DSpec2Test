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
    if s[i] <= ' ' {
      s' := s' + [ch];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ReplaceBlanksWithChar("", '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == ' ' ==> r0[i] == '\0') && (""[i] != ' ' ==> r0[i] == ""[i]);
}
method {:test} Test1() {
var r0 := ReplaceBlanksWithChar("a\U{0001}", '\0');
expect |r0| == |"a\U{0001}"|;
expect forall i :: 0 <= i < |"a\U{0001}"| ==> ("a\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}"[i] != ' ' ==> r0[i] == "a\U{0001}"[i]);
}
method {:test} Test2() {
var r0 := ReplaceBlanksWithChar(" ", '\0');
expect |r0| == |" "|;
expect forall i :: 0 <= i < |" "| ==> (" "[i] == ' ' ==> r0[i] == '\0') && (" "[i] != ' ' ==> r0[i] == " "[i]);
}

// REPEAT 1 - TIME: 3.2463713 s

method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("aa\U{0001}", '\0');
expect |r0| == |"aa\U{0001}"|;
expect forall i :: 0 <= i < |"aa\U{0001}"| ==> ("aa\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("aa\U{0001}"[i] != ' ' ==> r0[i] == "aa\U{0001}"[i]);
}
method {:test} Test4() {
var r0 := ReplaceBlanksWithChar("a\U{0001}a", '\0');
expect |r0| == |"a\U{0001}a"|;
expect forall i :: 0 <= i < |"a\U{0001}a"| ==> ("a\U{0001}a"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}a"[i] != ' ' ==> r0[i] == "a\U{0001}a"[i]);
}
method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("a a", '\0');
expect |r0| == |"a a"|;
expect forall i :: 0 <= i < |"a a"| ==> ("a a"[i] == ' ' ==> r0[i] == '\0') && ("a a"[i] != ' ' ==> r0[i] == "a a"[i]);
}

// REPEAT 2 - TIME: 5.0689295 s

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("\0aa\0aaaaaaaaaaaaaa\0", '\0');
expect |r0| == |"\0aa\0aaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\0aa\0aaaaaaaaaaaaaa\0"| ==> ("\0aa\0aaaaaaaaaaaaaa\0"[i] == ' ' ==> r0[i] == '\0') && ("\0aa\0aaaaaaaaaaaaaa\0"[i] != ' ' ==> r0[i] == "\0aa\0aaaaaaaaaaaaaa\0"[i]);
}
method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("\0\U{0001}", '\0');
expect |r0| == |"\0\U{0001}"|;
expect forall i :: 0 <= i < |"\0\U{0001}"| ==> ("\0\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\0\U{0001}"[i] != ' ' ==> r0[i] == "\0\U{0001}"[i]);
}
method {:test} Test8() {
var r0 := ReplaceBlanksWithChar("\0 aa", '\0');
expect |r0| == |"\0 aa"|;
expect forall i :: 0 <= i < |"\0 aa"| ==> ("\0 aa"[i] == ' ' ==> r0[i] == '\0') && ("\0 aa"[i] != ' ' ==> r0[i] == "\0 aa"[i]);
}

// REPEAT 3 - TIME: 7.2894863 s

method {:test} Test9() {
var r0 := ReplaceBlanksWithChar("\0aaaaaaaaaaaaaaaaaa\0", '\0');
expect |r0| == |"\0aaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaa\0"| ==> ("\0aaaaaaaaaaaaaaaaaa\0"[i] == ' ' ==> r0[i] == '\0') && ("\0aaaaaaaaaaaaaaaaaa\0"[i] != ' ' ==> r0[i] == "\0aaaaaaaaaaaaaaaaaa\0"[i]);
}
method {:test} Test10() {
var r0 := ReplaceBlanksWithChar("aa\0\0\0", '\0');
expect |r0| == |"aa\0\0\0"|;
expect forall i :: 0 <= i < |"aa\0\0\0"| ==> ("aa\0\0\0"[i] == ' ' ==> r0[i] == '\0') && ("aa\0\0\0"[i] != ' ' ==> r0[i] == "aa\0\0\0"[i]);
}
method {:test} Test11() {
var r0 := ReplaceBlanksWithChar(" a\0", ' ');
expect |r0| == |" a\0"|;
expect forall i :: 0 <= i < |" a\0"| ==> (" a\0"[i] == ' ' ==> r0[i] == ' ') && (" a\0"[i] != ' ' ==> r0[i] == " a\0"[i]);
}

// REPEAT 4 - TIME: 9.1028845 s

method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("\0a\0a\0\0aaaaaaaaaaaaa\0\0", '\0');
expect |r0| == |"\0a\0a\0\0aaaaaaaaaaaaa\0\0"|;
expect forall i :: 0 <= i < |"\0a\0a\0\0aaaaaaaaaaaaa\0\0"| ==> ("\0a\0a\0\0aaaaaaaaaaaaa\0\0"[i] == ' ' ==> r0[i] == '\0') && ("\0a\0a\0\0aaaaaaaaaaaaa\0\0"[i] != ' ' ==> r0[i] == "\0a\0a\0\0aaaaaaaaaaaaa\0\0"[i]);
}
method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test14() {
var r0 := ReplaceBlanksWithChar(" \U{0003}\U{0001}", '\0');
expect |r0| == |" \U{0003}\U{0001}"|;
expect forall i :: 0 <= i < |" \U{0003}\U{0001}"| ==> (" \U{0003}\U{0001}"[i] == ' ' ==> r0[i] == '\0') && (" \U{0003}\U{0001}"[i] != ' ' ==> r0[i] == " \U{0003}\U{0001}"[i]);
}

// REPEAT 5 - TIME: 10.561001 s

method {:test} Test15() {
var r0 := ReplaceBlanksWithChar("\0aaaa\0aaaaaaaaaaaaa\0aa", '\0');
expect |r0| == |"\0aaaa\0aaaaaaaaaaaaa\0aa"|;
expect forall i :: 0 <= i < |"\0aaaa\0aaaaaaaaaaaaa\0aa"| ==> ("\0aaaa\0aaaaaaaaaaaaa\0aa"[i] == ' ' ==> r0[i] == '\0') && ("\0aaaa\0aaaaaaaaaaaaa\0aa"[i] != ' ' ==> r0[i] == "\0aaaa\0aaaaaaaaaaaaa\0aa"[i]);
}
method {:test} Test16() {
var r0 := ReplaceBlanksWithChar("aaaaaaaa\U{0001}aaaaaaaaaaaaa", '\0');
expect |r0| == |"aaaaaaaa\U{0001}aaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaa\U{0001}aaaaaaaaaaaaa"| ==> ("aaaaaaaa\U{0001}aaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaa\U{0001}aaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaa\U{0001}aaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceBlanksWithChar("aaaaaa aaaaaaaaaaa", '\0');
expect |r0| == |"aaaaaa aaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaa aaaaaaaaaaa"| ==> ("aaaaaa aaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaa aaaaaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaa aaaaaaaaaaa"[i]);
}

// REPEAT 6 - TIME: 11.9049132 s

method {:test} Test18() {
var r0 := ReplaceBlanksWithChar("\0aa\0\0\0", '\0');
expect |r0| == |"\0aa\0\0\0"|;
expect forall i :: 0 <= i < |"\0aa\0\0\0"| ==> ("\0aa\0\0\0"[i] == ' ' ==> r0[i] == '\0') && ("\0aa\0\0\0"[i] != ' ' ==> r0[i] == "\0aa\0\0\0"[i]);
}
method {:test} Test19() {
var r0 := ReplaceBlanksWithChar("\0aaa\U{0001}\U{0003}", '\0');
expect |r0| == |"\0aaa\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |"\0aaa\U{0001}\U{0003}"| ==> ("\0aaa\U{0001}\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("\0aaa\U{0001}\U{0003}"[i] != ' ' ==> r0[i] == "\0aaa\U{0001}\U{0003}"[i]);
}
method {:test} Test20() {
var r0 := ReplaceBlanksWithChar("\U{0002}aaaa ", '\0');
expect |r0| == |"\U{0002}aaaa "|;
expect forall i :: 0 <= i < |"\U{0002}aaaa "| ==> ("\U{0002}aaaa "[i] == ' ' ==> r0[i] == '\0') && ("\U{0002}aaaa "[i] != ' ' ==> r0[i] == "\U{0002}aaaa "[i]);
}

// REPEAT 7 - TIME: 13.1728832 s

method {:test} Test21() {
var r0 := ReplaceBlanksWithChar("\0aaa\0aaaaa\0aaaaaaaa\0\0\0\0", '\0');
expect |r0| == |"\0aaa\0aaaaa\0aaaaaaaa\0\0\0\0"|;
expect forall i :: 0 <= i < |"\0aaa\0aaaaa\0aaaaaaaa\0\0\0\0"| ==> ("\0aaa\0aaaaa\0aaaaaaaa\0\0\0\0"[i] == ' ' ==> r0[i] == '\0') && ("\0aaa\0aaaaa\0aaaaaaaa\0\0\0\0"[i] != ' ' ==> r0[i] == "\0aaa\0aaaaa\0aaaaaaaa\0\0\0\0"[i]);
}
method {:test} Test22() {
var r0 := ReplaceBlanksWithChar("\0aaaa\U{0001}a", '\0');
expect |r0| == |"\0aaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"\0aaaa\U{0001}a"| ==> ("\0aaaa\U{0001}a"[i] == ' ' ==> r0[i] == '\0') && ("\0aaaa\U{0001}a"[i] != ' ' ==> r0[i] == "\0aaaa\U{0001}a"[i]);
}
method {:test} Test23() {
var r0 := ReplaceBlanksWithChar(" aaa aaaaaaaaaaaaaa\U{0006}\U{0004}\U{0002}a", '\0');
expect |r0| == |" aaa aaaaaaaaaaaaaa\U{0006}\U{0004}\U{0002}a"|;
expect forall i :: 0 <= i < |" aaa aaaaaaaaaaaaaa\U{0006}\U{0004}\U{0002}a"| ==> (" aaa aaaaaaaaaaaaaa\U{0006}\U{0004}\U{0002}a"[i] == ' ' ==> r0[i] == '\0') && (" aaa aaaaaaaaaaaaaa\U{0006}\U{0004}\U{0002}a"[i] != ' ' ==> r0[i] == " aaa aaaaaaaaaaaaaa\U{0006}\U{0004}\U{0002}a"[i]);
}

// REPEAT 8 - TIME: 14.711227 s

method {:test} Test24() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaa\U{0003}aaaaaaaaaaaaaa\U{0005}\U{0007}aa", '\0');
expect |r0| == |"\U{0001}aaaa\U{0003}aaaaaaaaaaaaaa\U{0005}\U{0007}aa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaa\U{0003}aaaaaaaaaaaaaa\U{0005}\U{0007}aa"| ==> ("\U{0001}aaaa\U{0003}aaaaaaaaaaaaaa\U{0005}\U{0007}aa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaa\U{0003}aaaaaaaaaaaaaa\U{0005}\U{0007}aa"[i] != ' ' ==> r0[i] == "\U{0001}aaaa\U{0003}aaaaaaaaaaaaaa\U{0005}\U{0007}aa"[i]);
}
method {:test} Test25() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaa"| ==> ("aaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaa"[i]);
}
method {:test} Test26() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaa\U{0002}aa", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaa\U{0002}aa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaa\U{0002}aa"| ==> (" aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i]);
}

// REPEAT 9 - TIME: 16.0927332 s

method {:test} Test27() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaa\U{0001}aaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaa\U{0001}aaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaa\U{0001}aaa"| ==> ("aaaaaaaaaaaaaaaaaaaaa\U{0001}aaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaa\U{0001}aaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaa\U{0001}aaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaa"| ==> ("\U{0001}aaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaa", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaa"| ==> (" aaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 17.7783344 s

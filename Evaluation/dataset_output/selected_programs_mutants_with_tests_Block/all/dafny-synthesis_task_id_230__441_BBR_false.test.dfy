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
    if false {
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

// REPEAT 1 - TIME: 3.1790899 s

method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test4() {
var r0 := ReplaceBlanksWithChar("a\U{0001}a", '\0');
expect |r0| == |"a\U{0001}a"|;
expect forall i :: 0 <= i < |"a\U{0001}a"| ==> ("a\U{0001}a"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}a"[i] != ' ' ==> r0[i] == "a\U{0001}a"[i]);
}
method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("\U{0002}aaaaaaaaaa ", '\0');
expect |r0| == |"\U{0002}aaaaaaaaaa "|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaa "| ==> ("\U{0002}aaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaa "[i] != ' ' ==> r0[i] == "\U{0002}aaaaaaaaaa "[i]);
}

// REPEAT 2 - TIME: 5.1030191 s

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaaaaaaa\U{0003}", '\0');
expect |r0| == |"\U{0001}aaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaa\U{0003}"| ==> ("\U{0001}aaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == "\U{0001}aaaaaaaaa\U{0003}"[i]);
}
method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("\U{0001}\U{0003}", '\0');
expect |r0| == |"\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0003}"| ==> ("\U{0001}\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}\U{0003}"[i] != ' ' ==> r0[i] == "\U{0001}\U{0003}"[i]);
}
method {:test} Test8() {
var r0 := ReplaceBlanksWithChar("\U{0002} ", '\0');
expect |r0| == |"\U{0002} "|;
expect forall i :: 0 <= i < |"\U{0002} "| ==> ("\U{0002} "[i] == ' ' ==> r0[i] == '\0') && ("\U{0002} "[i] != ' ' ==> r0[i] == "\U{0002} "[i]);
}

// REPEAT 3 - TIME: 6.7470677 s

method {:test} Test9() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test10() {
var r0 := ReplaceBlanksWithChar("a\U{0001}aa", '\0');
expect |r0| == |"a\U{0001}aa"|;
expect forall i :: 0 <= i < |"a\U{0001}aa"| ==> ("a\U{0001}aa"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}aa"[i] != ' ' ==> r0[i] == "a\U{0001}aa"[i]);
}
method {:test} Test11() {
var r0 := ReplaceBlanksWithChar(" aaa", '\0');
expect |r0| == |" aaa"|;
expect forall i :: 0 <= i < |" aaa"| ==> (" aaa"[i] == ' ' ==> r0[i] == '\0') && (" aaa"[i] != ' ' ==> r0[i] == " aaa"[i]);
}

// REPEAT 4 - TIME: 8.1474872 s

method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaa\U{0001}\U{0003}", '\0');
expect |r0| == |"aaaaaaaaaaa\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaa\U{0001}\U{0003}"| ==> ("aaaaaaaaaaa\U{0001}\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaa\U{0001}\U{0003}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaa\U{0001}\U{0003}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test14() {
var r0 := ReplaceBlanksWithChar("\U{0003} aa\U{0007}aaaa\U{0001}aaaa\U{0005}aaaaaaaaaaa\t", '\0');
expect |r0| == |"\U{0003} aa\U{0007}aaaa\U{0001}aaaa\U{0005}aaaaaaaaaaa\t"|;
expect forall i :: 0 <= i < |"\U{0003} aa\U{0007}aaaa\U{0001}aaaa\U{0005}aaaaaaaaaaa\t"| ==> ("\U{0003} aa\U{0007}aaaa\U{0001}aaaa\U{0005}aaaaaaaaaaa\t"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003} aa\U{0007}aaaa\U{0001}aaaa\U{0005}aaaaaaaaaaa\t"[i] != ' ' ==> r0[i] == "\U{0003} aa\U{0007}aaaa\U{0001}aaaa\U{0005}aaaaaaaaaaa\t"[i]);
}

// REPEAT 5 - TIME: 9.3508681 s

method {:test} Test15() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaaaaaaaaa\U{0007}\ta\U{0005}aaaaaaaaa\U{0003}a\U{000B}", '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaa\U{0007}\ta\U{0005}aaaaaaaaa\U{0003}a\U{000B}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaa\U{0007}\ta\U{0005}aaaaaaaaa\U{0003}a\U{000B}"| ==> ("\U{0001}aaaaaaaaaaa\U{0007}\ta\U{0005}aaaaaaaaa\U{0003}a\U{000B}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaa\U{0007}\ta\U{0005}aaaaaaaaa\U{0003}a\U{000B}"[i] != ' ' ==> r0[i] == "\U{0001}aaaaaaaaaaa\U{0007}\ta\U{0005}aaaaaaaaa\U{0003}a\U{000B}"[i]);
}
method {:test} Test16() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaaaaaaaaaaaaaa\U{0005}aaaaaaaa\U{0003}\U{0007}", '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaa\U{0005}aaaaaaaa\U{0003}\U{0007}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaa\U{0005}aaaaaaaa\U{0003}\U{0007}"| ==> ("\U{0001}aaaaaaaaaaaaaaaa\U{0005}aaaaaaaa\U{0003}\U{0007}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaa\U{0005}aaaaaaaa\U{0003}\U{0007}"[i] != ' ' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaa\U{0005}aaaaaaaa\U{0003}\U{0007}"[i]);
}
method {:test} Test17() {
var r0 := ReplaceBlanksWithChar(" aa\U{0001}\U{0003}", '\0');
expect |r0| == |" aa\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |" aa\U{0001}\U{0003}"| ==> (" aa\U{0001}\U{0003}"[i] == ' ' ==> r0[i] == '\0') && (" aa\U{0001}\U{0003}"[i] != ' ' ==> r0[i] == " aa\U{0001}\U{0003}"[i]);
}

// REPEAT 6 - TIME: 10.7134662 s

method {:test} Test18() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaa\U{0003}", '\0');
expect |r0| == |"\U{0001}aaaa\U{0003}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaa\U{0003}"| ==> ("\U{0001}aaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaa\U{0003}"[i] != ' ' ==> r0[i] == "\U{0001}aaaa\U{0003}"[i]);
}
method {:test} Test19() {
var r0 := ReplaceBlanksWithChar("\U{0001}aa\U{0003}\U{0005}\U{0007}", '\0');
expect |r0| == |"\U{0001}aa\U{0003}\U{0005}\U{0007}"|;
expect forall i :: 0 <= i < |"\U{0001}aa\U{0003}\U{0005}\U{0007}"| ==> ("\U{0001}aa\U{0003}\U{0005}\U{0007}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aa\U{0003}\U{0005}\U{0007}"[i] != ' ' ==> r0[i] == "\U{0001}aa\U{0003}\U{0005}\U{0007}"[i]);
}
method {:test} Test20() {
var r0 := ReplaceBlanksWithChar("\U{0003} aa\U{0007}aaaaaa\U{0001}\U{000B}\raaaaaaaa\U{0005}aaa\t\U{000F}a", '\0');
expect |r0| == |"\U{0003} aa\U{0007}aaaaaa\U{0001}\U{000B}\raaaaaaaa\U{0005}aaa\t\U{000F}a"|;
expect forall i :: 0 <= i < |"\U{0003} aa\U{0007}aaaaaa\U{0001}\U{000B}\raaaaaaaa\U{0005}aaa\t\U{000F}a"| ==> ("\U{0003} aa\U{0007}aaaaaa\U{0001}\U{000B}\raaaaaaaa\U{0005}aaa\t\U{000F}a"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003} aa\U{0007}aaaaaa\U{0001}\U{000B}\raaaaaaaa\U{0005}aaa\t\U{000F}a"[i] != ' ' ==> r0[i] == "\U{0003} aa\U{0007}aaaaaa\U{0001}\U{000B}\raaaaaaaa\U{0005}aaa\t\U{000F}a"[i]);
}

// REPEAT 7 - TIME: 12.1514975 s

method {:test} Test21() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaaaa\U{0003}aaaa\U{0005}\U{0007}", '\0');
expect |r0| == |"\U{0001}aaaaaa\U{0003}aaaa\U{0005}\U{0007}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaa\U{0003}aaaa\U{0005}\U{0007}"| ==> ("\U{0001}aaaaaa\U{0003}aaaa\U{0005}\U{0007}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaaaa\U{0003}aaaa\U{0005}\U{0007}"[i] != ' ' ==> r0[i] == "\U{0001}aaaaaa\U{0003}aaaa\U{0005}\U{0007}"[i]);
}
method {:test} Test22() {
var r0 := ReplaceBlanksWithChar("\U{0001}aa\U{0005}aaaa\U{0007}aaaaa\taa\raaaaa\U{0003}aa\U{000B}\U{000F}a\U{0011}", '\0');
expect |r0| == |"\U{0001}aa\U{0005}aaaa\U{0007}aaaaa\taa\raaaaa\U{0003}aa\U{000B}\U{000F}a\U{0011}"|;
expect forall i :: 0 <= i < |"\U{0001}aa\U{0005}aaaa\U{0007}aaaaa\taa\raaaaa\U{0003}aa\U{000B}\U{000F}a\U{0011}"| ==> ("\U{0001}aa\U{0005}aaaa\U{0007}aaaaa\taa\raaaaa\U{0003}aa\U{000B}\U{000F}a\U{0011}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aa\U{0005}aaaa\U{0007}aaaaa\taa\raaaaa\U{0003}aa\U{000B}\U{000F}a\U{0011}"[i] != ' ' ==> r0[i] == "\U{0001}aa\U{0005}aaaa\U{0007}aaaaa\taa\raaaaa\U{0003}aa\U{000B}\U{000F}a\U{0011}"[i]);
}
method {:test} Test23() {
var r0 := ReplaceBlanksWithChar("aaaa aaaaaa\U{0006}aaaaaaa\U{0004}aaa\U{0002}aaa\n\U{0008}a", '\0');
expect |r0| == |"aaaa aaaaaa\U{0006}aaaaaaa\U{0004}aaa\U{0002}aaa\n\U{0008}a"|;
expect forall i :: 0 <= i < |"aaaa aaaaaa\U{0006}aaaaaaa\U{0004}aaa\U{0002}aaa\n\U{0008}a"| ==> ("aaaa aaaaaa\U{0006}aaaaaaa\U{0004}aaa\U{0002}aaa\n\U{0008}a"[i] == ' ' ==> r0[i] == '\0') && ("aaaa aaaaaa\U{0006}aaaaaaa\U{0004}aaa\U{0002}aaa\n\U{0008}a"[i] != ' ' ==> r0[i] == "aaaa aaaaaa\U{0006}aaaaaaa\U{0004}aaa\U{0002}aaa\n\U{0008}a"[i]);
}

// REPEAT 8 - TIME: 13.8002295 s

method {:test} Test24() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaaa\U{0003}", '\0');
expect |r0| == |"\U{0001}aaaaa\U{0003}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaa\U{0003}"| ==> ("\U{0001}aaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaaa\U{0003}"[i] != ' ' ==> r0[i] == "\U{0001}aaaaa\U{0003}"[i]);
}
method {:test} Test25() {
var r0 := ReplaceBlanksWithChar("a\taaaaaaaaaaaa\U{0007}aaaaaaaa\U{0005}\U{0001}a\U{0003}", '\0');
expect |r0| == |"a\taaaaaaaaaaaa\U{0007}aaaaaaaa\U{0005}\U{0001}a\U{0003}"|;
expect forall i :: 0 <= i < |"a\taaaaaaaaaaaa\U{0007}aaaaaaaa\U{0005}\U{0001}a\U{0003}"| ==> ("a\taaaaaaaaaaaa\U{0007}aaaaaaaa\U{0005}\U{0001}a\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("a\taaaaaaaaaaaa\U{0007}aaaaaaaa\U{0005}\U{0001}a\U{0003}"[i] != ' ' ==> r0[i] == "a\taaaaaaaaaaaa\U{0007}aaaaaaaa\U{0005}\U{0001}a\U{0003}"[i]);
}
method {:test} Test26() {
var r0 := ReplaceBlanksWithChar("\U{0002}aaaaaa aaaaaaaaaa", '\0');
expect |r0| == |"\U{0002}aaaaaa aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaa aaaaaaaaaa"| ==> ("\U{0002}aaaaaa aaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0002}aaaaaa aaaaaaaaaa"[i] != ' ' ==> r0[i] == "\U{0002}aaaaaa aaaaaaaaaa"[i]);
}

// REPEAT 9 - TIME: 15.312313 s

method {:test} Test27() {
var r0 := ReplaceBlanksWithChar("\U{0001}aaaaaaaaaaaaaaa\U{0007}aaa\U{0003}\U{0005}aaaa", '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaa\U{0007}aaa\U{0003}\U{0005}aaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaa\U{0007}aaa\U{0003}\U{0005}aaaa"| ==> ("\U{0001}aaaaaaaaaaaaaaa\U{0007}aaa\U{0003}\U{0005}aaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaa\U{0007}aaa\U{0003}\U{0005}aaaa"[i] != ' ' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaa\U{0007}aaa\U{0003}\U{0005}aaaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceBlanksWithChar("\U{0004}aaaaaaaaaaaaaaaaa\U{0002}a aaaaa", '\0');
expect |r0| == |"\U{0004}aaaaaaaaaaaaaaaaa\U{0002}a aaaaa"|;
expect forall i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaa\U{0002}a aaaaa"| ==> ("\U{0004}aaaaaaaaaaaaaaaaa\U{0002}a aaaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0004}aaaaaaaaaaaaaaaaa\U{0002}a aaaaa"[i] != ' ' ==> r0[i] == "\U{0004}aaaaaaaaaaaaaaaaa\U{0002}a aaaaa"[i]);
}

// REPEAT 10 - TIME: 16.8917264 s

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


method {:testEntry} ReplaceBlanksWithChar(s: string, ch: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == ' ' ==> v[i] == ch) && (s[i] != ' ' ==> v[i] == s[i])
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == ' ' ==> s'[k] == ch) && (s[k] != ' ' ==> s'[k] == s[k])
    {
        if s[i] == ' '
        {
            s' := s' + [ch];
        }
        else 
        {
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
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test2() {
var r0 := ReplaceBlanksWithChar(" ", '\0');
expect |r0| == |" "|;
expect forall i :: 0 <= i < |" "| ==> (" "[i] == ' ' ==> r0[i] == '\0') && (" "[i] != ' ' ==> r0[i] == " "[i]);
}

// REPEAT 1 - TIME: 2.8356942 s

method {:test} Test3() {
var r0 := ReplaceBlanksWithChar("aa", '\0');
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> ("aa"[i] == ' ' ==> r0[i] == '\0') && ("aa"[i] != ' ' ==> r0[i] == "aa"[i]);
}
method {:test} Test4() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaa\U{0003}", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaa\U{0003}"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaa\U{0003}"| ==> (" aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaa\U{0003}"[i]);
}
method {:test} Test5() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaa ", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaa "| ==> ("aaaaaaaaaaaaaaaaaaaaaa "[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaa "[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaa "[i]);
}

// REPEAT 2 - TIME: 4.1384421 s

method {:test} Test6() {
var r0 := ReplaceBlanksWithChar("", '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == ' ' ==> r0[i] == '\0') && (""[i] != ' ' ==> r0[i] == ""[i]);
}
method {:test} Test7() {
var r0 := ReplaceBlanksWithChar("a\U{0001}a", '\0');
expect |r0| == |"a\U{0001}a"|;
expect forall i :: 0 <= i < |"a\U{0001}a"| ==> ("a\U{0001}a"[i] == ' ' ==> r0[i] == '\0') && ("a\U{0001}a"[i] != ' ' ==> r0[i] == "a\U{0001}a"[i]);
}
method {:test} Test8() {
var r0 := ReplaceBlanksWithChar(" aa", '\0');
expect |r0| == |" aa"|;
expect forall i :: 0 <= i < |" aa"| ==> (" aa"[i] == ' ' ==> r0[i] == '\0') && (" aa"[i] != ' ' ==> r0[i] == " aa"[i]);
}

// REPEAT 3 - TIME: 5.9693091 s

method {:test} Test9() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"| ==> (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa \U{0001}"[i]);
}
method {:test} Test10() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaa aaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaa aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaa aaaaaaaa"| ==> ("aaaaaaaaaaaaaaa aaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaa aaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaa aaaaaaaa"[i]);
}

// REPEAT 4 - TIME: 7.7600507 s

method {:test} Test12() {
var r0 := ReplaceBlanksWithChar("\U{0001}", '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}"[i] != ' ' ==> r0[i] == "\U{0001}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceBlanksWithChar("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa", '\0');
expect |r0| == |"\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"|;
expect forall i :: 0 <= i < |"\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"| ==> ("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i] == ' ' ==> r0[i] == '\0') && ("\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i] != ' ' ==> r0[i] == "\U{0003}aaaaaaaaa\U{0001}aaaaaaaaaaaa\U{0007}\taaaaaaaaaaaaaaa\U{0005}aaaa"[i]);
}
method {:test} Test14() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa", '\0');
expect |r0| == |"aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"| ==> ("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaa aaaaaaaaaaaa\U{0003}\U{0005}aaaaaaaaaaaaaaa\U{0001}aaaa"[i]);
}

// REPEAT 5 - TIME: 9.4719595 s

method {:test} Test15() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"| ==> ("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}"[i]);
}
method {:test} Test16() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 6 - TIME: 10.7628486 s

method {:test} Test18() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}\U{0005}"[i]);
}
method {:test} Test19() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{0001}aaaaa"[i]);
}
method {:test} Test20() {
var r0 := ReplaceBlanksWithChar(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && (" aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}

// REPEAT 7 - TIME: 12.086663 s

method {:test} Test21() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}"[i]);
}
method {:test} Test22() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"| ==> ("aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaa aaaaaaa\U{0002}a\U{0004}aaaaaaaaaaaaaaaaa\U{0008}\U{0006}\n\U{000C}"[i]);
}

// REPEAT 8 - TIME: 13.4233286 s

method {:test} Test24() {
var r0 := ReplaceBlanksWithChar("aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}", '\0');
expect |r0| == |"aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"|;
expect forall i :: 0 <= i < |"aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"| ==> ("aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"[i] == ' ' ==> r0[i] == '\0') && ("aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"[i] != ' ' ==> r0[i] == "aa\raaaaaaaaaaaaaaaaaaaaaa\U{0001}\U{0003}aaaaaaaaaaaaaaaaa\U{0005}\U{0007}\t\U{000B}\U{000F}"[i]);
}
method {:test} Test25() {
var r0 := ReplaceBlanksWithChar("\U{0001}\U{0005}a\U{0003}", '\0');
expect |r0| == |"\U{0001}\U{0005}a\U{0003}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0005}a\U{0003}"| ==> ("\U{0001}\U{0005}a\U{0003}"[i] == ' ' ==> r0[i] == '\0') && ("\U{0001}\U{0005}a\U{0003}"[i] != ' ' ==> r0[i] == "\U{0001}\U{0005}a\U{0003}"[i]);
}
method {:test} Test26() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaa"[i]);
}

// REPEAT 9 - TIME: 15.5365181 s

method {:test} Test27() {
var r0 := ReplaceBlanksWithChar("  aaaaaaaaaaaaaaaaaaaaaaaaaa", '\0');
expect |r0| == |"  aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"  aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> ("  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i] == ' ' ==> r0[i] == '\0') && ("  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i] != ' ' ==> r0[i] == "  aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}aa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceBlanksWithChar("aaaaaaaaaaaaaaaaaaaaaaaaa aa", '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa aa"| ==> ("aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i] == ' ' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i] != ' ' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa aa"[i]);
}

// REPEAT 10 - TIME: 17.1582654 s

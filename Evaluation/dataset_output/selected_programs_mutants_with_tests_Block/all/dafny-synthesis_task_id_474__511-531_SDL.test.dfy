// dafny-synthesis_task_id_474.dfy

method {:testEntry} ReplaceChars(s: string, oldChar: char, newChar: char)
    returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i ==> (s[k] == oldChar ==> s'[k] == newChar) && (s[k] != oldChar ==> s'[k] == s[k])
  {
    if s[i] == oldChar {
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ReplaceChars("", '\U{0001}', '\0');
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> (""[i] == '\U{0001}' ==> r0[i] == '\0') && (""[i] != '\U{0001}' ==> r0[i] == ""[i]);
}
method {:test} Test1() {
var r0 := ReplaceChars("\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0002}"| ==> ("\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0002}"[i]);
}
method {:test} Test2() {
var r0 := ReplaceChars("\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}"| ==> ("\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}"[i]);
}

// REPEAT 1 - TIME: 3.3074411 s

method {:test} Test3() {
var r0 := ReplaceChars("\0", '\U{0001}', '\0');
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> ("\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0"[i] != '\U{0001}' ==> r0[i] == "\0"[i]);
}
method {:test} Test4() {
var r0 := ReplaceChars("aaaaaa\U{0002}", '\U{0001}', '\0');
expect |r0| == |"aaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"aaaaaa\U{0002}"| ==> ("aaaaaa\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaa\U{0002}"[i] != '\U{0001}' ==> r0[i] == "aaaaaa\U{0002}"[i]);
}
method {:test} Test5() {
var r0 := ReplaceChars("aaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaa\U{0001}"| ==> ("aaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 5.0648229 s

method {:test} Test6() {
var r0 := ReplaceChars("\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"\U{0001}a"|;
expect forall i :: 0 <= i < |"\U{0001}a"| ==> ("\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "\U{0001}a"[i]);
}
method {:test} Test7() {
var r0 := ReplaceChars("\0\U{0003}", '\U{0001}', '\0');
expect |r0| == |"\0\U{0003}"|;
expect forall i :: 0 <= i < |"\0\U{0003}"| ==> ("\0\U{0003}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0\U{0003}"[i] != '\U{0001}' ==> r0[i] == "\0\U{0003}"[i]);
}
method {:test} Test8() {
var r0 := ReplaceChars("\0aa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\0aa\U{0001}"|;
expect forall i :: 0 <= i < |"\0aa\U{0001}"| ==> ("\0aa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\0aa\U{0001}"[i]);
}

// REPEAT 3 - TIME: 6.6392081 s

method {:test} Test9() {
var r0 := ReplaceChars("\0aa", '\U{0001}', '\0');
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> ("\0aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aa"[i] != '\U{0001}' ==> r0[i] == "\0aa"[i]);
}
method {:test} Test10() {
var r0 := ReplaceChars("\U{0001}\U{0002}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}\U{0002}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}\U{0002}\U{0001}"| ==> ("\U{0001}\U{0002}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}\U{0002}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}\U{0002}\U{0001}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceChars("\0\U{0001}a\U{0002}\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\0\U{0001}a\U{0002}\U{0004}"|;
expect forall i :: 0 <= i < |"\0\U{0001}a\U{0002}\U{0004}"| ==> ("\0\U{0001}a\U{0002}\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0\U{0001}a\U{0002}\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\0\U{0001}a\U{0002}\U{0004}"[i]);
}

// REPEAT 4 - TIME: 8.2966293 s

method {:test} Test12() {
var r0 := ReplaceChars("\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"| ==> ("\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaa\U{0001}\U{0001}aaaaaaa\U{0001}"[i]);
}
method {:test} Test13() {
var r0 := ReplaceChars("aaaa\U{0002}a", '\U{0001}', '\0');
expect |r0| == |"aaaa\U{0002}a"|;
expect forall i :: 0 <= i < |"aaaa\U{0002}a"| ==> ("aaaa\U{0002}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaa\U{0002}a"[i] != '\U{0001}' ==> r0[i] == "aaaa\U{0002}a"[i]);
}
method {:test} Test14() {
var r0 := ReplaceChars("\0a\U{0001}\U{0002}a\U{0004}a\0", '\U{0001}', '\0');
expect |r0| == |"\0a\U{0001}\U{0002}a\U{0004}a\0"|;
expect forall i :: 0 <= i < |"\0a\U{0001}\U{0002}a\U{0004}a\0"| ==> ("\0a\U{0001}\U{0002}a\U{0004}a\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\U{0001}\U{0002}a\U{0004}a\0"[i] != '\U{0001}' ==> r0[i] == "\0a\U{0001}\U{0002}a\U{0004}a\0"[i]);
}

// REPEAT 5 - TIME: 10.1766674 s

method {:test} Test15() {
var r0 := ReplaceChars("\0aa\0", '\U{0001}', '\0');
expect |r0| == |"\0aa\0"|;
expect forall i :: 0 <= i < |"\0aa\0"| ==> ("\0aa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aa\0"[i] != '\U{0001}' ==> r0[i] == "\0aa\0"[i]);
}
method {:test} Test16() {
var r0 := ReplaceChars("a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n", '\U{0001}', '\0');
expect |r0| == |"a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"|;
expect forall i :: 0 <= i < |"a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"| ==> ("a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"[i] != '\U{0001}' ==> r0[i] == "a\U{0002}aa\U{0004}\U{0006}a\U{0008}\n"[i]);
}
method {:test} Test17() {
var r0 := ReplaceChars("\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a", '\U{0001}', '\0');
expect |r0| == |"\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"|;
expect forall i :: 0 <= i < |"\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"| ==> ("\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"[i] != '\U{0001}' ==> r0[i] == "\0a\U{0001}aa\0a\U{0004}aa\0aaa\U{0006}\U{0002}a"[i]);
}

// REPEAT 6 - TIME: 12.0384769 s

method {:test} Test18() {
var r0 := ReplaceChars("\U{0001}aaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaa\U{0001}"| ==> ("\U{0001}aaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaa\U{0001}"[i]);
}
method {:test} Test19() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaa"| ==> ("\U{0002}aaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test20() {
var r0 := ReplaceChars("\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}aaaaa\U{0001}a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}aaaaa\U{0001}a\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}aaaaa\U{0001}a\U{0001}"| ==> ("\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}aaaaa\U{0001}a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}aaaaa\U{0001}a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}aaaaa\U{0001}a\U{0001}"[i]);
}

// REPEAT 7 - TIME: 13.716889 s

method {:test} Test21() {
var r0 := ReplaceChars("aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"| ==> ("aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "aaaaa\0aaaaaa\0aaaaaaaaaaaaaaa\0"[i]);
}
method {:test} Test22() {
var r0 := ReplaceChars("\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"| ==> ("\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaa\U{0001}aaa\U{0001}a\U{0001}aaaaaa\U{0001}aaaaaaaaaa\U{0001}"[i]);
}
method {:test} Test23() {
var r0 := ReplaceChars("aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}", '\U{0001}', '\0');
expect |r0| == |"aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"|;
expect forall i :: 0 <= i < |"aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"| ==> ("aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"[i] != '\U{0001}' ==> r0[i] == "aaaaa\0aaa\0aaaaaa\U{0001}a\U{0004}\U{0002}"[i]);
}

// REPEAT 8 - TIME: 15.1374727 s

method {:test} Test24() {
var r0 := ReplaceChars("\0aaaaaaaaaaaaaaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"\0aaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaa\0"| ==> ("\0aaaaaaaaaaaaaaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aaaaaaaaaaaaaaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "\0aaaaaaaaaaaaaaaaaaa\0"[i]);
}
method {:test} Test25() {
var r0 := ReplaceChars("a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa", '\U{0001}', '\0');
expect |r0| == |"a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"|;
expect forall i :: 0 <= i < |"a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"| ==> ("a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"[i] != '\U{0001}' ==> r0[i] == "a\U{0006}aaaaaaaaaaaaaaaa\U{0004}aaaaaaa\U{0002}aa"[i]);
}
method {:test} Test26() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"| ==> ("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}"[i]);
}

// REPEAT 9 - TIME: 16.8715415 s

method {:test} Test27() {
var r0 := ReplaceChars("aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"| ==> ("aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceChars("aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"| ==> ("aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaa\U{0002}aaaaaaa\U{0004}aaaaaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"| ==> ("\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaaaaa\U{0001}aaaaaaaaaa"[i]);
}

// REPEAT 10 - TIME: 18.426497 s

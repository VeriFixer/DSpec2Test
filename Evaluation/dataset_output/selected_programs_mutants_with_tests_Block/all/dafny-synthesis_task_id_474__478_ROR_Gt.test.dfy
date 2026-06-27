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
    if s[i] > oldChar {
      s' := s' + [newChar];
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

// REPEAT 1 - TIME: 3.5608077 s

method {:test} Test3() {
var r0 := ReplaceChars("\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0002}"| ==> ("\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0002}"[i]);
}
method {:test} Test5() {
var r0 := ReplaceChars("aaaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaa\U{0001}"| ==> ("aaaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 2 - TIME: 5.0939444 s

method {:test} Test6() {
var r0 := ReplaceChars("\0", '\U{0001}', '\0');
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> ("\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0"[i] != '\U{0001}' ==> r0[i] == "\0"[i]);
}
method {:test} Test7() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaa\U{0002}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaa\U{0002}"| ==> ("\U{0001}aaaaaaaaaa\U{0002}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaa\U{0002}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaa\U{0002}"[i]);
}
method {:test} Test8() {
var r0 := ReplaceChars("a\U{0001}", '\U{0001}', '\0');
expect |r0| == |"a\U{0001}"|;
expect forall i :: 0 <= i < |"a\U{0001}"| ==> ("a\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0001}"[i] != '\U{0001}' ==> r0[i] == "a\U{0001}"[i]);
}

// REPEAT 3 - TIME: 6.8135752 s

method {:test} Test9() {
var r0 := ReplaceChars("\0aaaaaa\0aaaa\0", '\U{0001}', '\0');
expect |r0| == |"\0aaaaaa\0aaaa\0"|;
expect forall i :: 0 <= i < |"\0aaaaaa\0aaaa\0"| ==> ("\0aaaaaa\0aaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aaaaaa\0aaaa\0"[i] != '\U{0001}' ==> r0[i] == "\0aaaaaa\0aaaa\0"[i]);
}
method {:test} Test10() {
var r0 := ReplaceChars("\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}", '\U{0001}', '\0');
expect |r0| == |"\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"|;
expect forall i :: 0 <= i < |"\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"| ==> ("\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"[i] != '\U{0001}' ==> r0[i] == "\0aaa\U{0002}aaaaaa\U{0004}\taaaaaa\U{0007}"[i]);
}
method {:test} Test11() {
var r0 := ReplaceChars("\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}", '\U{0001}', '\0');
expect |r0| == |"\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"| ==> ("\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"[i] != '\U{0001}' ==> r0[i] == "\0a\U{0001}aaaaaaa\U{0002}a\U{0006}aaaaaa\U{0004}"[i]);
}

// REPEAT 4 - TIME: 8.3766831 s

method {:test} Test12() {
var r0 := ReplaceChars("aa\0aaaaaaaaa\0aaaaaaa\0", '\U{0001}', '\0');
expect |r0| == |"aa\0aaaaaaaaa\0aaaaaaa\0"|;
expect forall i :: 0 <= i < |"aa\0aaaaaaaaa\0aaaaaaa\0"| ==> ("aa\0aaaaaaaaa\0aaaaaaa\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aa\0aaaaaaaaa\0aaaaaaa\0"[i] != '\U{0001}' ==> r0[i] == "aa\0aaaaaaaaa\0aaaaaaa\0"[i]);
}
method {:test} Test13() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaa"| ==> ("\U{0002}aaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaa"[i]);
}
method {:test} Test14() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaaaa"| ==> ("\U{0001}aaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaaaa"[i]);
}

// REPEAT 5 - TIME: 9.9432396 s

method {:test} Test15() {
var r0 := ReplaceChars("aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"| ==> ("aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaa\U{0001}aaaa\U{0001}aaaaaaaa\U{0001}a"[i]);
}
method {:test} Test16() {
var r0 := ReplaceChars("\U{0002}aaaaaaaaaaaaaaaaaaaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaa"| ==> ("\U{0002}aaaaaaaaaaaaaaaaaaaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aaaaaaaaaaaaaaaaaaaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaaa"[i]);
}
method {:test} Test17() {
var r0 := ReplaceChars("\0", '\0', '\0');
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> ("\0"[i] == '\0' ==> r0[i] == '\0') && ("\0"[i] != '\0' ==> r0[i] == "\0"[i]);
}

// REPEAT 6 - TIME: 11.8095745 s

method {:test} Test18() {
var r0 := ReplaceChars("\0a\0", '\U{0001}', '\0');
expect |r0| == |"\0a\0"|;
expect forall i :: 0 <= i < |"\0a\0"| ==> ("\0a\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\0a\0"[i] != '\U{0001}' ==> r0[i] == "\0a\0"[i]);
}
method {:test} Test19() {
var r0 := ReplaceChars("aaaaaaaaaaaaaaaaaaaa\U{0002}aa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{0002}aa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0002}aa"| ==> ("aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{0002}aa"[i]);
}
method {:test} Test20() {
var r0 := ReplaceChars("aaaaaaaaaa\U{0001}", '\U{0001}', '\0');
expect |r0| == |"aaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaa\U{0001}"| ==> ("aaaaaaaaaa\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaaaaa\U{0001}"[i] != '\U{0001}' ==> r0[i] == "aaaaaaaaaa\U{0001}"[i]);
}

// REPEAT 7 - TIME: 13.5141349 s

method {:test} Test21() {
var r0 := ReplaceChars("aaa\0aaaaaaaaaaaaaaaaaa\0\0aa\0a\0", '\U{0001}', '\0');
expect |r0| == |"aaa\0aaaaaaaaaaaaaaaaaa\0\0aa\0a\0"|;
expect forall i :: 0 <= i < |"aaa\0aaaaaaaaaaaaaaaaaa\0\0aa\0a\0"| ==> ("aaa\0aaaaaaaaaaaaaaaaaa\0\0aa\0a\0"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaa\0aaaaaaaaaaaaaaaaaa\0\0aa\0a\0"[i] != '\U{0001}' ==> r0[i] == "aaa\0aaaaaaaaaaaaaaaaaa\0\0aa\0a\0"[i]);
}
method {:test} Test22() {
var r0 := ReplaceChars("aaaaaaa\U{0002}aa", '\U{0001}', '\0');
expect |r0| == |"aaaaaaa\U{0002}aa"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0002}aa"| ==> ("aaaaaaa\U{0002}aa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaaaaaa\U{0002}aa"[i] != '\U{0001}' ==> r0[i] == "aaaaaaa\U{0002}aa"[i]);
}
method {:test} Test23() {
var r0 := ReplaceChars("\U{0001}aaaa\U{0001}aaaaaaa\U{0002}\U{0001}", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaa\U{0001}aaaaaaa\U{0002}\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0001}aaaa\U{0001}aaaaaaa\U{0002}\U{0001}"| ==> ("\U{0001}aaaa\U{0001}aaaaaaa\U{0002}\U{0001}"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaa\U{0001}aaaaaaa\U{0002}\U{0001}"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaa\U{0001}aaaaaaa\U{0002}\U{0001}"[i]);
}

// REPEAT 8 - TIME: 14.862874 s

method {:test} Test24() {
var r0 := ReplaceChars("aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a", '\U{0001}', '\0');
expect |r0| == |"aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"|;
expect forall i :: 0 <= i < |"aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"| ==> ("aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"[i] != '\U{0001}' ==> r0[i] == "aaa\U{0001}aaaaaaaaaaa\U{0001}aaaaaa\U{0001}aaaaa\U{0001}a"[i]);
}
method {:test} Test25() {
var r0 := ReplaceChars("a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta", '\U{0001}', '\0');
expect |r0| == |"a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"|;
expect forall i :: 0 <= i < |"a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"| ==> ("a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"[i] == '\U{0001}' ==> r0[i] == '\0') && ("a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"[i] != '\U{0001}' ==> r0[i] == "a\U{0002}a\U{0004}aaaaaaaaaaa\U{0001}aaaaa\U{0001}\U{0007}\U{0001}aa\U{0001}a\ta"[i]);
}
method {:test} Test26() {
var r0 := ReplaceChars("\0aaa", '\0', '\0');
expect |r0| == |"\0aaa"|;
expect forall i :: 0 <= i < |"\0aaa"| ==> ("\0aaa"[i] == '\0' ==> r0[i] == '\0') && ("\0aaa"[i] != '\0' ==> r0[i] == "\0aaa"[i]);
}

// REPEAT 9 - TIME: 16.2785801 s

method {:test} Test27() {
var r0 := ReplaceChars("aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa", '\U{0001}', '\0');
expect |r0| == |"aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"|;
expect forall i :: 0 <= i < |"aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"| ==> ("aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"[i] != '\U{0001}' ==> r0[i] == "aaa\0aaaaaaaaaaa\0aaaaaaa\0aaa"[i]);
}
method {:test} Test28() {
var r0 := ReplaceChars("\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa", '\U{0001}', '\0');
expect |r0| == |"\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"|;
expect forall i :: 0 <= i < |"\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"| ==> ("\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"[i] != '\U{0001}' ==> r0[i] == "\U{0002}aa\U{0004}aaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa"[i]);
}
method {:test} Test29() {
var r0 := ReplaceChars("\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa", '\U{0001}', '\0');
expect |r0| == |"\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"|;
expect forall i :: 0 <= i < |"\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"| ==> ("\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"[i] == '\U{0001}' ==> r0[i] == '\0') && ("\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"[i] != '\U{0001}' ==> r0[i] == "\U{0001}aaaaaaaaaaa\U{0002}\U{0004}\U{0008}\U{0006}aaaaa\U{0001}\n\U{000C}aaaa"[i]);
}

// REPEAT 10 - TIME: 17.6839142 s

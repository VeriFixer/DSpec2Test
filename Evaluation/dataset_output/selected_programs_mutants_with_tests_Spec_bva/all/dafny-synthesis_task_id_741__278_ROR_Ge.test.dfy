// dafny-synthesis_task_id_741.dfy

method {:testEntry} AllCharactersSame(s: string) returns (result: bool)
  ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
  ensures !result ==> |s| > 1 && exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j]
{
  if |s| >= 1 {
    return true;
  }
  var firstChar := s[0];
  result := true;
  for i := 1 to |s|
    invariant 0 <= i <= |s|
    invariant result ==> forall k :: 0 <= k < i ==> s[k] == firstChar
  {
    if s[i] != firstChar {
      result := false;
      break;
    }
  }
}


method {:test} Test0() {
var r0 := AllCharactersSame("\0\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\0\U{0002}"| && 0 <= j < |"\0\U{0002}"| ==> "\0\U{0002}"[i] == "\0\U{0002}"[j];
expect !r0 ==> |"\0\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\0\U{0002}"| && 0 <= j < |"\0\U{0002}"| && i != j && "\0\U{0002}"[i] != "\0\U{0002}"[j];
}
method {:test} Test2() {
var r0 := AllCharactersSame("\U{0002}\0");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0002}\0"| && 0 <= j < |"\U{0002}\0"| ==> "\U{0002}\0"[i] == "\U{0002}\0"[j];
expect !r0 ==> |"\U{0002}\0"| > 1 && exists i, j :: 0 <= i < |"\U{0002}\0"| && 0 <= j < |"\U{0002}\0"| && i != j && "\U{0002}\0"[i] != "\U{0002}\0"[j];
}
method {:test} Test6() {
var r0 := AllCharactersSame("");
expect r0 ==> forall i, j :: 0 <= i < |""| && 0 <= j < |""| ==> ""[i] == ""[j];
expect !r0 ==> |""| > 1 && exists i, j :: 0 <= i < |""| && 0 <= j < |""| && i != j && ""[i] != ""[j];
}
method {:test} Test8() {
var r0 := AllCharactersSame("a");
expect r0 ==> forall i, j :: 0 <= i < |"a"| && 0 <= j < |"a"| ==> "a"[i] == "a"[j];
expect !r0 ==> |"a"| > 1 && exists i, j :: 0 <= i < |"a"| && 0 <= j < |"a"| && i != j && "a"[i] != "a"[j];
}
method {:test} Test9() {
var r0 := AllCharactersSame("aa");
expect r0 ==> forall i, j :: 0 <= i < |"aa"| && 0 <= j < |"aa"| ==> "aa"[i] == "aa"[j];
expect !r0 ==> |"aa"| > 1 && exists i, j :: 0 <= i < |"aa"| && 0 <= j < |"aa"| && i != j && "aa"[i] != "aa"[j];
}

// REPEAT 1 - TIME: 11.957748 s

method {:test} Test14() {
var r0 := AllCharactersSame("\U{0002}\0aaaaaaaaaaaaaa\U{0004}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0002}\0aaaaaaaaaaaaaa\U{0004}"| && 0 <= j < |"\U{0002}\0aaaaaaaaaaaaaa\U{0004}"| ==> "\U{0002}\0aaaaaaaaaaaaaa\U{0004}"[i] == "\U{0002}\0aaaaaaaaaaaaaa\U{0004}"[j];
expect !r0 ==> |"\U{0002}\0aaaaaaaaaaaaaa\U{0004}"| > 1 && exists i, j :: 0 <= i < |"\U{0002}\0aaaaaaaaaaaaaa\U{0004}"| && 0 <= j < |"\U{0002}\0aaaaaaaaaaaaaa\U{0004}"| && i != j && "\U{0002}\0aaaaaaaaaaaaaa\U{0004}"[i] != "\U{0002}\0aaaaaaaaaaaaaa\U{0004}"[j];
}
method {:test} Test15() {
var r0 := AllCharactersSame("aaa");
expect r0 ==> forall i, j :: 0 <= i < |"aaa"| && 0 <= j < |"aaa"| ==> "aaa"[i] == "aaa"[j];
expect !r0 ==> |"aaa"| > 1 && exists i, j :: 0 <= i < |"aaa"| && 0 <= j < |"aaa"| && i != j && "aaa"[i] != "aaa"[j];
}

// REPEAT 2 - TIME: 13.5656978 s

method {:test} Test16() {
var r0 := AllCharactersSame("\U{0002}\U{0004}\0a");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0002}\U{0004}\0a"| && 0 <= j < |"\U{0002}\U{0004}\0a"| ==> "\U{0002}\U{0004}\0a"[i] == "\U{0002}\U{0004}\0a"[j];
expect !r0 ==> |"\U{0002}\U{0004}\0a"| > 1 && exists i, j :: 0 <= i < |"\U{0002}\U{0004}\0a"| && 0 <= j < |"\U{0002}\U{0004}\0a"| && i != j && "\U{0002}\U{0004}\0a"[i] != "\U{0002}\U{0004}\0a"[j];
}
method {:test} Test17() {
var r0 := AllCharactersSame("\0aaaaaaa\0aaaaaa\0a\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0aaaaaaa\0aaaaaa\0a\0"| && 0 <= j < |"\0aaaaaaa\0aaaaaa\0a\0"| ==> "\0aaaaaaa\0aaaaaa\0a\0"[i] == "\0aaaaaaa\0aaaaaa\0a\0"[j];
expect !r0 ==> |"\0aaaaaaa\0aaaaaa\0a\0"| > 1 && exists i, j :: 0 <= i < |"\0aaaaaaa\0aaaaaa\0a\0"| && 0 <= j < |"\0aaaaaaa\0aaaaaa\0a\0"| && i != j && "\0aaaaaaa\0aaaaaa\0a\0"[i] != "\0aaaaaaa\0aaaaaa\0a\0"[j];
}

// REPEAT 3 - TIME: 14.96341 s

method {:test} Test18() {
var r0 := AllCharactersSame("\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"| && 0 <= j < |"\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"| ==> "\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"[i] == "\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"[j];
expect !r0 ==> |"\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"| > 1 && exists i, j :: 0 <= i < |"\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"| && 0 <= j < |"\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"| && i != j && "\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"[i] != "\U{0002}a\U{0006}\U{0008}aaa\0aaaaaaaaa\U{0004}a"[j];
}
method {:test} Test19() {
var r0 := AllCharactersSame("\0aaa\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0aaa\0"| && 0 <= j < |"\0aaa\0"| ==> "\0aaa\0"[i] == "\0aaa\0"[j];
expect !r0 ==> |"\0aaa\0"| > 1 && exists i, j :: 0 <= i < |"\0aaa\0"| && 0 <= j < |"\0aaa\0"| && i != j && "\0aaa\0"[i] != "\0aaa\0"[j];
}

// REPEAT 4 - TIME: 16.5641556 s

method {:test} Test20() {
var r0 := AllCharactersSame("\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"| && 0 <= j < |"\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"| ==> "\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"[i] == "\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"[j];
expect !r0 ==> |"\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"| && 0 <= j < |"\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"| && i != j && "\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"[i] != "\U{0002}a\0\U{0008}aaaaaaaaaaaaa\U{0004}\U{0006}"[j];
}
method {:test} Test21() {
var r0 := AllCharactersSame("\0\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0\0"| && 0 <= j < |"\0\0\0"| ==> "\0\0\0"[i] == "\0\0\0"[j];
expect !r0 ==> |"\0\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0\0"| && 0 <= j < |"\0\0\0"| && i != j && "\0\0\0"[i] != "\0\0\0"[j];
}

// REPEAT 5 - TIME: 18.1018119 s

method {:test} Test22() {
var r0 := AllCharactersSame("\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"| && 0 <= j < |"\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"| ==> "\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"[i] == "\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"[j];
expect !r0 ==> |"\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"| && 0 <= j < |"\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"| && i != j && "\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"[i] != "\U{0004}aaaa\U{0008}aaa\U{0002}\U{0006}aa\U{000E}\U{0010}aa\n\0\U{000C}"[j];
}
method {:test} Test23() {
var r0 := AllCharactersSame("\0aa\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0aa\0"| && 0 <= j < |"\0aa\0"| ==> "\0aa\0"[i] == "\0aa\0"[j];
expect !r0 ==> |"\0aa\0"| > 1 && exists i, j :: 0 <= i < |"\0aa\0"| && 0 <= j < |"\0aa\0"| && i != j && "\0aa\0"[i] != "\0aa\0"[j];
}

// REPEAT 6 - TIME: 19.6410288 s

method {:test} Test24() {
var r0 := AllCharactersSame("\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"| && 0 <= j < |"\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"| ==> "\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"[i] == "\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"[j];
expect !r0 ==> |"\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"| && 0 <= j < |"\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"| && i != j && "\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"[i] != "\U{000E}aaaaaaaa\U{0004}\U{0008}aa\U{0002}\0aa\U{000C}\n\U{0006}"[j];
}
method {:test} Test25() {
var r0 := AllCharactersSame("\0\0a\0\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0a\0\0\0"| && 0 <= j < |"\0\0a\0\0\0"| ==> "\0\0a\0\0\0"[i] == "\0\0a\0\0\0"[j];
expect !r0 ==> |"\0\0a\0\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0a\0\0\0"| && 0 <= j < |"\0\0a\0\0\0"| && i != j && "\0\0a\0\0\0"[i] != "\0\0a\0\0\0"[j];
}

// REPEAT 7 - TIME: 21.3190115 s

method {:test} Test26() {
var r0 := AllCharactersSame("\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"| && 0 <= j < |"\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"| ==> "\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"[i] == "\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"[j];
expect !r0 ==> |"\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"| > 1 && exists i, j :: 0 <= i < |"\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"| && 0 <= j < |"\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"| && i != j && "\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"[i] != "\U{0002}\0aaa\U{0008}aaa\U{0004}\U{0006}aaaaaa\n\U{000C}a\U{000E}"[j];
}
method {:test} Test27() {
var r0 := AllCharactersSame("\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"| && 0 <= j < |"\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"| ==> "\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"[i] == "\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"[j];
expect !r0 ==> |"\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"| > 1 && exists i, j :: 0 <= i < |"\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"| && 0 <= j < |"\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"| && i != j && "\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"[i] != "\0\0a\0a\0a\0\0aaaa\0a\0a\0a\0\0aaaa\0"[j];
}

// REPEAT 8 - TIME: 22.5566999 s

method {:test} Test28() {
var r0 := AllCharactersSame("\U{0004}\0a\U{0002}\U{0008}\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}\0a\U{0002}\U{0008}\U{0006}"| && 0 <= j < |"\U{0004}\0a\U{0002}\U{0008}\U{0006}"| ==> "\U{0004}\0a\U{0002}\U{0008}\U{0006}"[i] == "\U{0004}\0a\U{0002}\U{0008}\U{0006}"[j];
expect !r0 ==> |"\U{0004}\0a\U{0002}\U{0008}\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}\0a\U{0002}\U{0008}\U{0006}"| && 0 <= j < |"\U{0004}\0a\U{0002}\U{0008}\U{0006}"| && i != j && "\U{0004}\0a\U{0002}\U{0008}\U{0006}"[i] != "\U{0004}\0a\U{0002}\U{0008}\U{0006}"[j];
}
method {:test} Test29() {
var r0 := AllCharactersSame("\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0"| && 0 <= j < |"\0\0"| ==> "\0\0"[i] == "\0\0"[j];
expect !r0 ==> |"\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0"| && 0 <= j < |"\0\0"| && i != j && "\0\0"[i] != "\0\0"[j];
}

// REPEAT 9 - TIME: 24.2589897 s

method {:test} Test30() {
var r0 := AllCharactersSame("\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"| && 0 <= j < |"\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"| ==> "\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"[i] == "\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"[j];
expect !r0 ==> |"\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"| > 1 && exists i, j :: 0 <= i < |"\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"| && 0 <= j < |"\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"| && i != j && "\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"[i] != "\U{0014}aaa\U{0008}\U{0004}\U{000C}aa\naa\U{0002}\U{0006}\0aa\U{000E}\U{0010}\U{0012}"[j];
}
method {:test} Test31() {
var r0 := AllCharactersSame("\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"| && 0 <= j < |"\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"| ==> "\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"[i] == "\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"[j];
expect !r0 ==> |"\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"| > 1 && exists i, j :: 0 <= i < |"\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"| && 0 <= j < |"\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"| && i != j && "\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"[i] != "\0aaaaaa\0aaaaaaa\0a\0\0\0\0\0\0a\0a\0"[j];
}

// REPEAT 10 - TIME: 25.8148835 s

// dafny-synthesis_task_id_741.dfy

method {:testEntry} AllCharactersSame(s: string) returns (result: bool)
  ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
  ensures !result ==> |s| > 1 && exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j]
{
  var firstChar := s[0];
  if |s| <= 1 {
    return true;
  }
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

// REPEAT 1 - TIME: 9.1268833 s

method {:test} Test14() {
var r0 := AllCharactersSame("\U{0004}\0\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}\0\U{0002}"| && 0 <= j < |"\U{0004}\0\U{0002}"| ==> "\U{0004}\0\U{0002}"[i] == "\U{0004}\0\U{0002}"[j];
expect !r0 ==> |"\U{0004}\0\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}\0\U{0002}"| && 0 <= j < |"\U{0004}\0\U{0002}"| && i != j && "\U{0004}\0\U{0002}"[i] != "\U{0004}\0\U{0002}"[j];
}
method {:test} Test15() {
var r0 := AllCharactersSame("\0\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0\0"| && 0 <= j < |"\0\0\0"| ==> "\0\0\0"[i] == "\0\0\0"[j];
expect !r0 ==> |"\0\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0\0"| && 0 <= j < |"\0\0\0"| && i != j && "\0\0\0"[i] != "\0\0\0"[j];
}

// REPEAT 2 - TIME: 10.0321154 s

method {:test} Test16() {
var r0 := AllCharactersSame("\U{0002}a\0\U{0004}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0002}a\0\U{0004}"| && 0 <= j < |"\U{0002}a\0\U{0004}"| ==> "\U{0002}a\0\U{0004}"[i] == "\U{0002}a\0\U{0004}"[j];
expect !r0 ==> |"\U{0002}a\0\U{0004}"| > 1 && exists i, j :: 0 <= i < |"\U{0002}a\0\U{0004}"| && 0 <= j < |"\U{0002}a\0\U{0004}"| && i != j && "\U{0002}a\0\U{0004}"[i] != "\U{0002}a\0\U{0004}"[j];
}
method {:test} Test17() {
var r0 := AllCharactersSame("\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"| && 0 <= j < |"\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"| ==> "\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == "\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"[j];
expect !r0 ==> |"\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"| > 1 && exists i, j :: 0 <= i < |"\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"| && 0 <= j < |"\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"| && i != j && "\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"[i] != "\0a\0aaaaaaaaaaaaaaaaaaaaaaaa\0"[j];
}

// REPEAT 3 - TIME: 11.0253469 s

method {:test} Test18() {
var r0 := AllCharactersSame("\U{0006}\U{0002}\0\U{0004}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0006}\U{0002}\0\U{0004}"| && 0 <= j < |"\U{0006}\U{0002}\0\U{0004}"| ==> "\U{0006}\U{0002}\0\U{0004}"[i] == "\U{0006}\U{0002}\0\U{0004}"[j];
expect !r0 ==> |"\U{0006}\U{0002}\0\U{0004}"| > 1 && exists i, j :: 0 <= i < |"\U{0006}\U{0002}\0\U{0004}"| && 0 <= j < |"\U{0006}\U{0002}\0\U{0004}"| && i != j && "\U{0006}\U{0002}\0\U{0004}"[i] != "\U{0006}\U{0002}\0\U{0004}"[j];
}
method {:test} Test19() {
var r0 := AllCharactersSame("\0\0\0\0aaaaaaaaaaaaaaaaaaa\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"| && 0 <= j < |"\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"| ==> "\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"[i] == "\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"[j];
expect !r0 ==> |"\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"| > 1 && exists i, j :: 0 <= i < |"\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"| && 0 <= j < |"\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"| && i != j && "\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"[i] != "\0\0\0\0aaaaaaaaaaaaaaaaaaa\0"[j];
}

// REPEAT 4 - TIME: 12.1066958 s

method {:test} Test20() {
var r0 := AllCharactersSame("\U{0008}\U{0002}\0\U{0006}\U{0004}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0008}\U{0002}\0\U{0006}\U{0004}"| && 0 <= j < |"\U{0008}\U{0002}\0\U{0006}\U{0004}"| ==> "\U{0008}\U{0002}\0\U{0006}\U{0004}"[i] == "\U{0008}\U{0002}\0\U{0006}\U{0004}"[j];
expect !r0 ==> |"\U{0008}\U{0002}\0\U{0006}\U{0004}"| > 1 && exists i, j :: 0 <= i < |"\U{0008}\U{0002}\0\U{0006}\U{0004}"| && 0 <= j < |"\U{0008}\U{0002}\0\U{0006}\U{0004}"| && i != j && "\U{0008}\U{0002}\0\U{0006}\U{0004}"[i] != "\U{0008}\U{0002}\0\U{0006}\U{0004}"[j];
}
method {:test} Test21() {
var r0 := AllCharactersSame("\0\0a\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0a\0\0"| && 0 <= j < |"\0\0a\0\0"| ==> "\0\0a\0\0"[i] == "\0\0a\0\0"[j];
expect !r0 ==> |"\0\0a\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0a\0\0"| && 0 <= j < |"\0\0a\0\0"| && i != j && "\0\0a\0\0"[i] != "\0\0a\0\0"[j];
}

// REPEAT 5 - TIME: 13.0292729 s

method {:test} Test22() {
var r0 := AllCharactersSame("\U{0004}\na\U{0002}a\0\U{0008}\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"| && 0 <= j < |"\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"| ==> "\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"[i] == "\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"[j];
expect !r0 ==> |"\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"| && 0 <= j < |"\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"| && i != j && "\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"[i] != "\U{0004}\na\U{0002}a\0\U{0008}\U{0006}"[j];
}
method {:test} Test23() {
var r0 := AllCharactersSame("\0aa\0\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0aa\0\0\0"| && 0 <= j < |"\0aa\0\0\0"| ==> "\0aa\0\0\0"[i] == "\0aa\0\0\0"[j];
expect !r0 ==> |"\0aa\0\0\0"| > 1 && exists i, j :: 0 <= i < |"\0aa\0\0\0"| && 0 <= j < |"\0aa\0\0\0"| && i != j && "\0aa\0\0\0"[i] != "\0aa\0\0\0"[j];
}

// REPEAT 6 - TIME: 14.0899996 s

method {:test} Test24() {
var r0 := AllCharactersSame("\U{0004}a\U{0002}\0\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}a\U{0002}\0\U{0006}"| && 0 <= j < |"\U{0004}a\U{0002}\0\U{0006}"| ==> "\U{0004}a\U{0002}\0\U{0006}"[i] == "\U{0004}a\U{0002}\0\U{0006}"[j];
expect !r0 ==> |"\U{0004}a\U{0002}\0\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}a\U{0002}\0\U{0006}"| && 0 <= j < |"\U{0004}a\U{0002}\0\U{0006}"| && i != j && "\U{0004}a\U{0002}\0\U{0006}"[i] != "\U{0004}a\U{0002}\0\U{0006}"[j];
}
method {:test} Test25() {
var r0 := AllCharactersSame("\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"| && 0 <= j < |"\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"| ==> "\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"[i] == "\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"[j];
expect !r0 ==> |"\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"| > 1 && exists i, j :: 0 <= i < |"\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"| && 0 <= j < |"\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"| && i != j && "\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"[i] != "\0\0aaa\0aaa\0\0aaaaaaa\0aaaa\0a\0a\0a"[j];
}

// REPEAT 7 - TIME: 15.1802291 s

method {:test} Test26() {
var r0 := AllCharactersSame("\U{0004}\n\U{0002}a\0\U{0008}\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"| && 0 <= j < |"\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"| ==> "\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"[i] == "\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"[j];
expect !r0 ==> |"\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"| && 0 <= j < |"\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"| && i != j && "\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"[i] != "\U{0004}\n\U{0002}a\0\U{0008}\U{0006}"[j];
}
method {:test} Test27() {
var r0 := AllCharactersSame("\0\0a");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0a"| && 0 <= j < |"\0\0a"| ==> "\0\0a"[i] == "\0\0a"[j];
expect !r0 ==> |"\0\0a"| > 1 && exists i, j :: 0 <= i < |"\0\0a"| && 0 <= j < |"\0\0a"| && i != j && "\0\0a"[i] != "\0\0a"[j];
}

// REPEAT 8 - TIME: 16.3663187 s

method {:test} Test28() {
var r0 := AllCharactersSame("\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n");
expect r0 ==> forall i, j :: 0 <= i < |"\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"| && 0 <= j < |"\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"| ==> "\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"[i] == "\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"[j];
expect !r0 ==> |"\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"| > 1 && exists i, j :: 0 <= i < |"\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"| && 0 <= j < |"\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"| && i != j && "\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"[i] != "\U{000C}aa\0\U{0002}\U{0004}\U{0006}\U{0008}\n"[j];
}
method {:test} Test29() {
var r0 := AllCharactersSame("\0\0aa\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0aa\0\0"| && 0 <= j < |"\0\0aa\0\0"| ==> "\0\0aa\0\0"[i] == "\0\0aa\0\0"[j];
expect !r0 ==> |"\0\0aa\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0aa\0\0"| && 0 <= j < |"\0\0aa\0\0"| && i != j && "\0\0aa\0\0"[i] != "\0\0aa\0\0"[j];
}

// REPEAT 9 - TIME: 17.4254998 s

method {:test} Test30() {
var r0 := AllCharactersSame("\U{0004}\0a\U{0002}\U{0006}\U{0008}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}\0a\U{0002}\U{0006}\U{0008}"| && 0 <= j < |"\U{0004}\0a\U{0002}\U{0006}\U{0008}"| ==> "\U{0004}\0a\U{0002}\U{0006}\U{0008}"[i] == "\U{0004}\0a\U{0002}\U{0006}\U{0008}"[j];
expect !r0 ==> |"\U{0004}\0a\U{0002}\U{0006}\U{0008}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}\0a\U{0002}\U{0006}\U{0008}"| && 0 <= j < |"\U{0004}\0a\U{0002}\U{0006}\U{0008}"| && i != j && "\U{0004}\0a\U{0002}\U{0006}\U{0008}"[i] != "\U{0004}\0a\U{0002}\U{0006}\U{0008}"[j];
}
method {:test} Test31() {
var r0 := AllCharactersSame("\0\0\0\0a\0a\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0\0\0a\0a\0"| && 0 <= j < |"\0\0\0\0a\0a\0"| ==> "\0\0\0\0a\0a\0"[i] == "\0\0\0\0a\0a\0"[j];
expect !r0 ==> |"\0\0\0\0a\0a\0"| > 1 && exists i, j :: 0 <= i < |"\0\0\0\0a\0a\0"| && 0 <= j < |"\0\0\0\0a\0a\0"| && i != j && "\0\0\0\0a\0a\0"[i] != "\0\0\0\0a\0a\0"[j];
}

// REPEAT 10 - TIME: 18.4400943 s

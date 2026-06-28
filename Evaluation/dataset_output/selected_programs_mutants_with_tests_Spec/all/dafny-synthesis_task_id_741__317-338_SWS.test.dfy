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
method {:test} Test1() {
var r0 := AllCharactersSame("");
expect r0 ==> forall i, j :: 0 <= i < |""| && 0 <= j < |""| ==> ""[i] == ""[j];
expect !r0 ==> |""| > 1 && exists i, j :: 0 <= i < |""| && 0 <= j < |""| && i != j && ""[i] != ""[j];
}

// REPEAT 1 - TIME: 3.1965636 s

method {:test} Test2() {
var r0 := AllCharactersSame("\0\U{0002}a");
expect r0 ==> forall i, j :: 0 <= i < |"\0\U{0002}a"| && 0 <= j < |"\0\U{0002}a"| ==> "\0\U{0002}a"[i] == "\0\U{0002}a"[j];
expect !r0 ==> |"\0\U{0002}a"| > 1 && exists i, j :: 0 <= i < |"\0\U{0002}a"| && 0 <= j < |"\0\U{0002}a"| && i != j && "\0\U{0002}a"[i] != "\0\U{0002}a"[j];
}
method {:test} Test3() {
var r0 := AllCharactersSame("\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0"| && 0 <= j < |"\0"| ==> "\0"[i] == "\0"[j];
expect !r0 ==> |"\0"| > 1 && exists i, j :: 0 <= i < |"\0"| && 0 <= j < |"\0"| && i != j && "\0"[i] != "\0"[j];
}

// REPEAT 2 - TIME: 4.5218878 s

method {:test} Test4() {
var r0 := AllCharactersSame("aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"| && 0 <= j < |"aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"| ==> "aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"[i] == "aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"[j];
expect !r0 ==> |"aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"| > 1 && exists i, j :: 0 <= i < |"aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"| && 0 <= j < |"aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"| && i != j && "aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"[i] != "aa\U{0002}\0aaaaaaaaaa\U{0004}aaaa\U{0006}"[j];
}
method {:test} Test5() {
var r0 := AllCharactersSame("\0aa");
expect r0 ==> forall i, j :: 0 <= i < |"\0aa"| && 0 <= j < |"\0aa"| ==> "\0aa"[i] == "\0aa"[j];
expect !r0 ==> |"\0aa"| > 1 && exists i, j :: 0 <= i < |"\0aa"| && 0 <= j < |"\0aa"| && i != j && "\0aa"[i] != "\0aa"[j];
}

// REPEAT 3 - TIME: 6.1584594 s

method {:test} Test6() {
var r0 := AllCharactersSame("\U{0004}a\U{0002}\0");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}a\U{0002}\0"| && 0 <= j < |"\U{0004}a\U{0002}\0"| ==> "\U{0004}a\U{0002}\0"[i] == "\U{0004}a\U{0002}\0"[j];
expect !r0 ==> |"\U{0004}a\U{0002}\0"| > 1 && exists i, j :: 0 <= i < |"\U{0004}a\U{0002}\0"| && 0 <= j < |"\U{0004}a\U{0002}\0"| && i != j && "\U{0004}a\U{0002}\0"[i] != "\U{0004}a\U{0002}\0"[j];
}
method {:test} Test7() {
var r0 := AllCharactersSame("\0\0aaa\0aaaaaaaaaaaaaa\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0aaa\0aaaaaaaaaaaaaa\0"| && 0 <= j < |"\0\0aaa\0aaaaaaaaaaaaaa\0"| ==> "\0\0aaa\0aaaaaaaaaaaaaa\0"[i] == "\0\0aaa\0aaaaaaaaaaaaaa\0"[j];
expect !r0 ==> |"\0\0aaa\0aaaaaaaaaaaaaa\0"| > 1 && exists i, j :: 0 <= i < |"\0\0aaa\0aaaaaaaaaaaaaa\0"| && 0 <= j < |"\0\0aaa\0aaaaaaaaaaaaaa\0"| && i != j && "\0\0aaa\0aaaaaaaaaaaaaa\0"[i] != "\0\0aaa\0aaaaaaaaaaaaaa\0"[j];
}

// REPEAT 4 - TIME: 7.803712 s

method {:test} Test8() {
var r0 := AllCharactersSame("\U{0004}a\0\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0004}a\0\U{0002}"| && 0 <= j < |"\U{0004}a\0\U{0002}"| ==> "\U{0004}a\0\U{0002}"[i] == "\U{0004}a\0\U{0002}"[j];
expect !r0 ==> |"\U{0004}a\0\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\U{0004}a\0\U{0002}"| && 0 <= j < |"\U{0004}a\0\U{0002}"| && i != j && "\U{0004}a\0\U{0002}"[i] != "\U{0004}a\0\U{0002}"[j];
}
method {:test} Test9() {
var r0 := AllCharactersSame("\0\0\0a");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0\0a"| && 0 <= j < |"\0\0\0a"| ==> "\0\0\0a"[i] == "\0\0\0a"[j];
expect !r0 ==> |"\0\0\0a"| > 1 && exists i, j :: 0 <= i < |"\0\0\0a"| && 0 <= j < |"\0\0\0a"| && i != j && "\0\0\0a"[i] != "\0\0\0a"[j];
}

// REPEAT 5 - TIME: 9.2349989 s

method {:test} Test10() {
var r0 := AllCharactersSame("\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"| && 0 <= j < |"\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"| ==> "\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"[i] == "\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"[j];
expect !r0 ==> |"\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"| && 0 <= j < |"\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"| && i != j && "\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"[i] != "\U{0008}\0a\U{0002}aaaaa\U{0004}aaaaaaaaaa\U{0006}"[j];
}
method {:test} Test11() {
var r0 := AllCharactersSame("\0a\0a\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0a\0a\0"| && 0 <= j < |"\0a\0a\0"| ==> "\0a\0a\0"[i] == "\0a\0a\0"[j];
expect !r0 ==> |"\0a\0a\0"| > 1 && exists i, j :: 0 <= i < |"\0a\0a\0"| && 0 <= j < |"\0a\0a\0"| && i != j && "\0a\0a\0"[i] != "\0a\0a\0"[j];
}

// REPEAT 6 - TIME: 10.3025947 s

method {:test} Test12() {
var r0 := AllCharactersSame("\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a");
expect r0 ==> forall i, j :: 0 <= i < |"\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"| && 0 <= j < |"\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"| ==> "\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"[i] == "\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"[j];
expect !r0 ==> |"\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"| > 1 && exists i, j :: 0 <= i < |"\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"| && 0 <= j < |"\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"| && i != j && "\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"[i] != "\naaaaaa\U{0002}\U{0008}\0aaaaaaaa\U{0006}\U{0004}\U{000C}a"[j];
}
method {:test} Test13() {
var r0 := AllCharactersSame("\0\0aaa\0aaaaaaaaaaa\0\0a\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0aaa\0aaaaaaaaaaa\0\0a\0"| && 0 <= j < |"\0\0aaa\0aaaaaaaaaaa\0\0a\0"| ==> "\0\0aaa\0aaaaaaaaaaa\0\0a\0"[i] == "\0\0aaa\0aaaaaaaaaaa\0\0a\0"[j];
expect !r0 ==> |"\0\0aaa\0aaaaaaaaaaa\0\0a\0"| > 1 && exists i, j :: 0 <= i < |"\0\0aaa\0aaaaaaaaaaa\0\0a\0"| && 0 <= j < |"\0\0aaa\0aaaaaaaaaaa\0\0a\0"| && i != j && "\0\0aaa\0aaaaaaaaaaa\0\0a\0"[i] != "\0\0aaa\0aaaaaaaaaaa\0\0a\0"[j];
}

// REPEAT 7 - TIME: 11.4563035 s

method {:test} Test14() {
var r0 := AllCharactersSame("\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"| && 0 <= j < |"\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"| ==> "\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"[i] == "\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"[j];
expect !r0 ==> |"\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"| > 1 && exists i, j :: 0 <= i < |"\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"| && 0 <= j < |"\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"| && i != j && "\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"[i] != "\U{0008}aaaaaa\U{0002}\U{0006}\0aaaaaaaaa\U{0004}\n\U{000C}"[j];
}
method {:test} Test15() {
var r0 := AllCharactersSame("\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"| && 0 <= j < |"\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"| ==> "\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"[i] == "\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"[j];
expect !r0 ==> |"\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"| > 1 && exists i, j :: 0 <= i < |"\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"| && 0 <= j < |"\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"| && i != j && "\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"[i] != "\0\0aa\0aaaaaaaaa\0aaaaa\0\0\0"[j];
}

// REPEAT 8 - TIME: 12.416677 s

method {:test} Test16() {
var r0 := AllCharactersSame("\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}");
expect r0 ==> forall i, j :: 0 <= i < |"\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"| && 0 <= j < |"\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"| ==> "\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"[i] == "\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"[j];
expect !r0 ==> |"\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"| > 1 && exists i, j :: 0 <= i < |"\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"| && 0 <= j < |"\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"| && i != j && "\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"[i] != "\0aaaa\U{0004}aa\n\U{000C}aaaaaaaa\U{0002}a\U{0006}\U{0008}"[j];
}
method {:test} Test17() {
var r0 := AllCharactersSame("\0\0a\0a\0");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0a\0a\0"| && 0 <= j < |"\0\0a\0a\0"| ==> "\0\0a\0a\0"[i] == "\0\0a\0a\0"[j];
expect !r0 ==> |"\0\0a\0a\0"| > 1 && exists i, j :: 0 <= i < |"\0\0a\0a\0"| && 0 <= j < |"\0\0a\0a\0"| && i != j && "\0\0a\0a\0"[i] != "\0\0a\0a\0"[j];
}

// REPEAT 9 - TIME: 13.5075427 s

method {:test} Test18() {
var r0 := AllCharactersSame("\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"| && 0 <= j < |"\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"| ==> "\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"[i] == "\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"[j];
expect !r0 ==> |"\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"| > 1 && exists i, j :: 0 <= i < |"\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"| && 0 <= j < |"\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"| && i != j && "\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"[i] != "\U{0006}a\U{0004}aa\U{000E}aa\0\U{0002}aaaaaaaaa\n\U{0010}\U{0008}\U{000C}a"[j];
}
method {:test} Test19() {
var r0 := AllCharactersSame("\0\0a\0a");
expect r0 ==> forall i, j :: 0 <= i < |"\0\0a\0a"| && 0 <= j < |"\0\0a\0a"| ==> "\0\0a\0a"[i] == "\0\0a\0a"[j];
expect !r0 ==> |"\0\0a\0a"| > 1 && exists i, j :: 0 <= i < |"\0\0a\0a"| && 0 <= j < |"\0\0a\0a"| && i != j && "\0\0a\0a"[i] != "\0\0a\0a"[j];
}

// REPEAT 10 - TIME: 14.8216642 s

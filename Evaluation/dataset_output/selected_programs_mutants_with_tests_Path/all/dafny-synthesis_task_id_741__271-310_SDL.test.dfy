// dafny-synthesis_task_id_741.dfy

method {:testEntry} AllCharactersSame(s: string) returns (result: bool)
  ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
  ensures !result ==> |s| > 1 && exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j]
{
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
var r0 := AllCharactersSame("a");
expect r0 ==> forall i, j :: 0 <= i < |"a"| && 0 <= j < |"a"| ==> "a"[i] == "a"[j];
expect !r0 ==> |"a"| > 1 && exists i, j :: 0 <= i < |"a"| && 0 <= j < |"a"| && i != j && "a"[i] != "a"[j];
}
method {:test} Test1() {
var r0 := AllCharactersSame("\U{0001}a");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}a"| && 0 <= j < |"\U{0001}a"| ==> "\U{0001}a"[i] == "\U{0001}a"[j];
expect !r0 ==> |"\U{0001}a"| > 1 && exists i, j :: 0 <= i < |"\U{0001}a"| && 0 <= j < |"\U{0001}a"| && i != j && "\U{0001}a"[i] != "\U{0001}a"[j];
}
method {:test} Test2() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaa\U{0003}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaa\U{0003}"| && 0 <= j < |"\U{0001}aaaaaaaaa\U{0003}"| ==> "\U{0001}aaaaaaaaa\U{0003}"[i] == "\U{0001}aaaaaaaaa\U{0003}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaa\U{0003}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaa\U{0003}"| && 0 <= j < |"\U{0001}aaaaaaaaa\U{0003}"| && i != j && "\U{0001}aaaaaaaaa\U{0003}"[i] != "\U{0001}aaaaaaaaa\U{0003}"[j];
}

// REPEAT 1 - TIME: 12.2259435 s

method {:test} Test3() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test4() {
var r0 := AllCharactersSame("\U{0001}aaaaaa\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaa\U{0001}"| && 0 <= j < |"\U{0001}aaaaaa\U{0001}"| ==> "\U{0001}aaaaaa\U{0001}"[i] == "\U{0001}aaaaaa\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaaaa\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaa\U{0001}"| && 0 <= j < |"\U{0001}aaaaaa\U{0001}"| && i != j && "\U{0001}aaaaaa\U{0001}"[i] != "\U{0001}aaaaaa\U{0001}"[j];
}
method {:test} Test5() {
var r0 := AllCharactersSame("\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"| && 0 <= j < |"\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"| ==> "\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"[i] == "\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"[j];
expect !r0 ==> |"\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"| && 0 <= j < |"\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"| && i != j && "\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"[i] != "\U{0001}aa\U{0007}aaaaaa\U{0002}aaaaa\U{0004}"[j];
}

// REPEAT 2 - TIME: 21.7691656 s

method {:test} Test6() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test7() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"| ==> "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[i] == "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"| && i != j && "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[i] != "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0001}"[j];
}
method {:test} Test8() {
var r0 := AllCharactersSame("\U{0001}\U{0004}\U{0002}aaaaa\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"| && 0 <= j < |"\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"| ==> "\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"[i] == "\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"[j];
expect !r0 ==> |"\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"| && 0 <= j < |"\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"| && i != j && "\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"[i] != "\U{0001}\U{0004}\U{0002}aaaaa\U{0006}"[j];
}

// REPEAT 3 - TIME: 30.9340311 s

method {:test} Test9() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test10() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaa");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaa"| && 0 <= j < |"\U{0001}aaaaaaaaa"| ==> "\U{0001}aaaaaaaaa"[i] == "\U{0001}aaaaaaaaa"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaa"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaa"| && 0 <= j < |"\U{0001}aaaaaaaaa"| && i != j && "\U{0001}aaaaaaaaa"[i] != "\U{0001}aaaaaaaaa"[j];
}
method {:test} Test11() {
var r0 := AllCharactersSame("\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"| && 0 <= j < |"\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"| ==> "\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"[i] == "\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"| && 0 <= j < |"\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"| && i != j && "\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"[i] != "\U{0001}aaaa\U{0003}aaaaaaaaa\U{0001}a\U{0001}"[j];
}

// REPEAT 4 - TIME: 41.82432 s

method {:test} Test12() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test13() {
var r0 := AllCharactersSame("\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"| ==> "\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"[i] == "\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"| && i != j && "\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"[i] != "\U{0001}aa\U{0001}aaaa\U{0001}\U{0001}aaaaaaa\U{0001}\U{0001}"[j];
}
method {:test} Test14() {
var r0 := AllCharactersSame("\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"| && 0 <= j < |"\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"| ==> "\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"[i] == "\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"[j];
expect !r0 ==> |"\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"| && 0 <= j < |"\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"| && i != j && "\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"[i] != "\U{0001}\na\U{0006}aaaa\U{0004}aaaaaaa\U{0002}\U{0008}\U{000C}"[j];
}

// REPEAT 5 - TIME: 51.4196457 s

method {:test} Test15() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test16() {
var r0 := AllCharactersSame("\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"| && 0 <= j < |"\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"| ==> "\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"[i] == "\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"[j];
expect !r0 ==> |"\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"| && 0 <= j < |"\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"| && i != j && "\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"[i] != "\U{0001}a\U{0001}aaaa\U{0001}a\U{0001}a\U{0001}\U{0001}aaaa\U{0001}aaa\U{0001}"[j];
}
method {:test} Test17() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"| && 0 <= j < |"\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"| ==> "\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"[i] == "\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"| && 0 <= j < |"\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"| && i != j && "\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"[i] != "\U{0001}aaaaaaaaa\taaaaa\U{0003}\U{0007}a\U{0005}"[j];
}

// REPEAT 6 - TIME: 66.0750797 s

method {:test} Test18() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test19() {
var r0 := AllCharactersSame("\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"| ==> "\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"[i] == "\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"[j];
expect !r0 ==> |"\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"| && i != j && "\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"[i] != "\U{0001}a\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}a\U{0001}\U{0001}\U{0001}"[j];
}
method {:test} Test20() {
var r0 := AllCharactersSame("\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"| ==> "\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"[i] == "\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"| && i != j && "\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"[i] != "\U{0001}aa\U{0001}aa\U{0003}\U{0001}aa\U{0001}\U{0001}"[j];
}

// REPEAT 7 - TIME: 84.2174643 s

method {:test} Test21() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test22() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"| ==> "\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"[i] == "\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"| && i != j && "\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"[i] != "\U{0001}aaaaaaaaaa\U{0001}aa\U{0001}aa\U{0001}\U{0001}\U{0001}\U{0001}"[j];
}
method {:test} Test23() {
var r0 := AllCharactersSame("\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"| ==> "\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"[i] == "\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"[j];
expect !r0 ==> |"\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"| && i != j && "\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"[i] != "\U{0001}\U{0001}\U{0003}aaa\U{0001}aa\U{0001}\U{0001}"[j];
}

// REPEAT 8 - TIME: 105.7262676 s

method {:test} Test24() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test25() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"| && 0 <= j < |"\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"| ==> "\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"[i] == "\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"| && 0 <= j < |"\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"| && i != j && "\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"[i] != "\U{0001}aaaaaaaaa\U{0001}aaa\U{0001}\U{0001}\U{0001}\U{0001}aa\U{0001}aa"[j];
}
method {:test} Test26() {
var r0 := AllCharactersSame("\U{0001}\U{0001}aa\U{0003}a\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0001}aa\U{0003}a\U{0001}"| && 0 <= j < |"\U{0001}\U{0001}aa\U{0003}a\U{0001}"| ==> "\U{0001}\U{0001}aa\U{0003}a\U{0001}"[i] == "\U{0001}\U{0001}aa\U{0003}a\U{0001}"[j];
expect !r0 ==> |"\U{0001}\U{0001}aa\U{0003}a\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0001}aa\U{0003}a\U{0001}"| && 0 <= j < |"\U{0001}\U{0001}aa\U{0003}a\U{0001}"| && i != j && "\U{0001}\U{0001}aa\U{0003}a\U{0001}"[i] != "\U{0001}\U{0001}aa\U{0003}a\U{0001}"[j];
}

// REPEAT 9 - TIME: 129.4534042 s

method {:test} Test27() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}
method {:test} Test28() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"| ==> "\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"[i] == "\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"| && i != j && "\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"[i] != "\U{0001}aaaaaaaaaaaaa\U{0001}a\U{0001}\U{0001}\U{0001}\U{0001}a\U{0001}\U{0001}"[j];
}
method {:test} Test29() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"| ==> "\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"[i] == "\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"| && i != j && "\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"[i] != "\U{0001}aaaaaaaa\U{0001}aaa\U{0001}aa\U{0002}aaaaa\U{0001}\U{0001}"[j];
}

// REPEAT 10 - TIME: 148.485944 s

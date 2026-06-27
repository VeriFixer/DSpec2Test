// dafny-synthesis_task_id_741.dfy

method {:testEntry} AllCharactersSame(s: string) returns (result: bool)
  ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
  ensures !result ==> |s| > 1 && exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j]
{
  if |s| == 1 {
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
var r0 := AllCharactersSame("\U{0001}\U{0003}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0003}"| && 0 <= j < |"\U{0001}\U{0003}"| ==> "\U{0001}\U{0003}"[i] == "\U{0001}\U{0003}"[j];
expect !r0 ==> |"\U{0001}\U{0003}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0003}"| && 0 <= j < |"\U{0001}\U{0003}"| && i != j && "\U{0001}\U{0003}"[i] != "\U{0001}\U{0003}"[j];
}
method {:test} Test1() {
var r0 := AllCharactersSame("a");
expect r0 ==> forall i, j :: 0 <= i < |"a"| && 0 <= j < |"a"| ==> "a"[i] == "a"[j];
expect !r0 ==> |"a"| > 1 && exists i, j :: 0 <= i < |"a"| && 0 <= j < |"a"| && i != j && "a"[i] != "a"[j];
}

// REPEAT 1 - TIME: 3.0897195 s

method {:test} Test2() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"| ==> "\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[i] == "\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"| && i != j && "\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[i] != "\U{0001}aaaaaaaaaaaaaaaaa\U{0003}\U{0001}"[j];
}
method {:test} Test3() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 2 - TIME: 4.6001153 s

method {:test} Test4() {
var r0 := AllCharactersSame("\U{0001}aaaa\U{0003}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaa\U{0003}\U{0001}"| && 0 <= j < |"\U{0001}aaaa\U{0003}\U{0001}"| ==> "\U{0001}aaaa\U{0003}\U{0001}"[i] == "\U{0001}aaaa\U{0003}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaa\U{0003}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaa\U{0003}\U{0001}"| && 0 <= j < |"\U{0001}aaaa\U{0003}\U{0001}"| && i != j && "\U{0001}aaaa\U{0003}\U{0001}"[i] != "\U{0001}aaaa\U{0003}\U{0001}"[j];
}
method {:test} Test5() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 3 - TIME: 6.1129995 s

method {:test} Test6() {
var r0 := AllCharactersSame("\U{0001}\U{0003}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0003}"| && 0 <= j < |"\U{0001}\U{0003}"| ==> "\U{0001}\U{0003}"[i] == "\U{0001}\U{0003}"[j];
expect !r0 ==> |"\U{0001}\U{0003}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0003}"| && 0 <= j < |"\U{0001}\U{0003}"| && i != j && "\U{0001}\U{0003}"[i] != "\U{0001}\U{0003}"[j];
}
method {:test} Test7() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 4 - TIME: 7.6894387 s

method {:test} Test8() {
var r0 := AllCharactersSame("\U{0001}\U{0002}a");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0002}a"| && 0 <= j < |"\U{0001}\U{0002}a"| ==> "\U{0001}\U{0002}a"[i] == "\U{0001}\U{0002}a"[j];
expect !r0 ==> |"\U{0001}\U{0002}a"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0002}a"| && 0 <= j < |"\U{0001}\U{0002}a"| && i != j && "\U{0001}\U{0002}a"[i] != "\U{0001}\U{0002}a"[j];
}
method {:test} Test9() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 5 - TIME: 8.8837124 s

method {:test} Test10() {
var r0 := AllCharactersSame("\U{0001}\U{0005}\U{0003}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0005}\U{0003}"| && 0 <= j < |"\U{0001}\U{0005}\U{0003}"| ==> "\U{0001}\U{0005}\U{0003}"[i] == "\U{0001}\U{0005}\U{0003}"[j];
expect !r0 ==> |"\U{0001}\U{0005}\U{0003}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0005}\U{0003}"| && 0 <= j < |"\U{0001}\U{0005}\U{0003}"| && i != j && "\U{0001}\U{0005}\U{0003}"[i] != "\U{0001}\U{0005}\U{0003}"[j];
}
method {:test} Test11() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 6 - TIME: 9.8387977 s

method {:test} Test12() {
var r0 := AllCharactersSame("\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"| && 0 <= j < |"\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"| ==> "\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"[i] == "\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"[j];
expect !r0 ==> |"\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"| && 0 <= j < |"\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"| && i != j && "\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"[i] != "\U{0001}\U{0004}a\U{0002}aaaaa\U{0006}"[j];
}
method {:test} Test13() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 7 - TIME: 11.0550949 s

method {:test} Test14() {
var r0 := AllCharactersSame("\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"| && 0 <= j < |"\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"| ==> "\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"[i] == "\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"[j];
expect !r0 ==> |"\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"| && 0 <= j < |"\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"| && i != j && "\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"[i] != "\U{0001}\U{0006}aaaaaaa\U{0002}\U{0004}aaaaaa\U{0008}"[j];
}
method {:test} Test15() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 8 - TIME: 12.4690141 s

method {:test} Test16() {
var r0 := AllCharactersSame("\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"| ==> "\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"[i] == "\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"| && i != j && "\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"[i] != "\U{0001}aaaaaa\U{0001}aaaaaa\U{0001}\U{0001}aa\U{0001}\U{0001}aaaaaaa\U{0002}\U{0001}"[j];
}
method {:test} Test17() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 9 - TIME: 13.7255962 s

method {:test} Test18() {
var r0 := AllCharactersSame("\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"| && 0 <= j < |"\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"| ==> "\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"[i] == "\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"[j];
expect !r0 ==> |"\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"| && 0 <= j < |"\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"| && i != j && "\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"[i] != "\U{0001}\U{0001}aaa\U{0001}a\U{0001}\U{0002}a\U{0001}a\U{0001}aaaa\U{0001}"[j];
}
method {:test} Test19() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 10 - TIME: 14.934491 s

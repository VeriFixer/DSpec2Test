// dafny-synthesis_task_id_741.dfy

method {:testEntry} AllCharactersSame(s: string) returns (result: bool)
  ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
  ensures !result ==> |s| > 1 && exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j]
{
  if |s| != 1 {
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

// REPEAT 1 - TIME: 3.4302604 s

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

// REPEAT 2 - TIME: 4.8612392 s

method {:test} Test4() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"| ==> "\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"[i] == "\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"| && i != j && "\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"[i] != "\U{0001}aaaaaaaaaaaaaaaaaa\U{0002}\U{0001}"[j];
}
method {:test} Test5() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 3 - TIME: 6.2676915 s

method {:test} Test6() {
var r0 := AllCharactersSame("\U{0001}\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0002}"| && 0 <= j < |"\U{0001}\U{0002}"| ==> "\U{0001}\U{0002}"[i] == "\U{0001}\U{0002}"[j];
expect !r0 ==> |"\U{0001}\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0002}"| && 0 <= j < |"\U{0001}\U{0002}"| && i != j && "\U{0001}\U{0002}"[i] != "\U{0001}\U{0002}"[j];
}
method {:test} Test7() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 4 - TIME: 7.6931478 s

method {:test} Test8() {
var r0 := AllCharactersSame("\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"| ==> "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"[i] == "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"[j];
expect !r0 ==> |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"| && 0 <= j < |"\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"| && i != j && "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"[i] != "\U{0001}aaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}"[j];
}
method {:test} Test9() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 5 - TIME: 8.9320631 s

method {:test} Test10() {
var r0 := AllCharactersSame("\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"| && 0 <= j < |"\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"| ==> "\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"[i] == "\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"[j];
expect !r0 ==> |"\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"| && 0 <= j < |"\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"| && i != j && "\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"[i] != "\U{0001}\U{0001}aaaaaaaaa\U{0001}aaaaa\U{0002}\U{0001}"[j];
}
method {:test} Test11() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 6 - TIME: 10.4023196 s

method {:test} Test12() {
var r0 := AllCharactersSame("\U{0001}\U{0003}aaa");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0003}aaa"| && 0 <= j < |"\U{0001}\U{0003}aaa"| ==> "\U{0001}\U{0003}aaa"[i] == "\U{0001}\U{0003}aaa"[j];
expect !r0 ==> |"\U{0001}\U{0003}aaa"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0003}aaa"| && 0 <= j < |"\U{0001}\U{0003}aaa"| && i != j && "\U{0001}\U{0003}aaa"[i] != "\U{0001}\U{0003}aaa"[j];
}
method {:test} Test13() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 7 - TIME: 11.6554389 s

method {:test} Test14() {
var r0 := AllCharactersSame("\U{0001}\U{0005}aaa\U{0003}aa");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0005}aaa\U{0003}aa"| && 0 <= j < |"\U{0001}\U{0005}aaa\U{0003}aa"| ==> "\U{0001}\U{0005}aaa\U{0003}aa"[i] == "\U{0001}\U{0005}aaa\U{0003}aa"[j];
expect !r0 ==> |"\U{0001}\U{0005}aaa\U{0003}aa"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0005}aaa\U{0003}aa"| && 0 <= j < |"\U{0001}\U{0005}aaa\U{0003}aa"| && i != j && "\U{0001}\U{0005}aaa\U{0003}aa"[i] != "\U{0001}\U{0005}aaa\U{0003}aa"[j];
}
method {:test} Test15() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 8 - TIME: 12.9367495 s

method {:test} Test16() {
var r0 := AllCharactersSame("\U{0001}\U{0001}\U{0001}\U{0002}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0001}\U{0001}\U{0002}"| && 0 <= j < |"\U{0001}\U{0001}\U{0001}\U{0002}"| ==> "\U{0001}\U{0001}\U{0001}\U{0002}"[i] == "\U{0001}\U{0001}\U{0001}\U{0002}"[j];
expect !r0 ==> |"\U{0001}\U{0001}\U{0001}\U{0002}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0001}\U{0001}\U{0002}"| && 0 <= j < |"\U{0001}\U{0001}\U{0001}\U{0002}"| && i != j && "\U{0001}\U{0001}\U{0001}\U{0002}"[i] != "\U{0001}\U{0001}\U{0001}\U{0002}"[j];
}
method {:test} Test17() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 9 - TIME: 14.0928255 s

method {:test} Test18() {
var r0 := AllCharactersSame("\U{0001}\U{0002}\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}\U{0002}\U{0001}"| && 0 <= j < |"\U{0001}\U{0002}\U{0001}"| ==> "\U{0001}\U{0002}\U{0001}"[i] == "\U{0001}\U{0002}\U{0001}"[j];
expect !r0 ==> |"\U{0001}\U{0002}\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}\U{0002}\U{0001}"| && 0 <= j < |"\U{0001}\U{0002}\U{0001}"| && i != j && "\U{0001}\U{0002}\U{0001}"[i] != "\U{0001}\U{0002}\U{0001}"[j];
}
method {:test} Test19() {
var r0 := AllCharactersSame("\U{0001}");
expect r0 ==> forall i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| ==> "\U{0001}"[i] == "\U{0001}"[j];
expect !r0 ==> |"\U{0001}"| > 1 && exists i, j :: 0 <= i < |"\U{0001}"| && 0 <= j < |"\U{0001}"| && i != j && "\U{0001}"[i] != "\U{0001}"[j];
}

// REPEAT 10 - TIME: 14.962074 s

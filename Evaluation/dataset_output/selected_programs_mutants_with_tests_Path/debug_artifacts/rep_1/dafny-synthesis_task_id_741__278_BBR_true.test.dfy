// dafny-synthesis_task_id_741.dfy

method {:testEntry} AllCharactersSame(s: string) returns (result: bool)
  ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
  ensures !result ==> |s| > 1 && exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j]
{
  if true {
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

// REPEAT 1 - TIME: 9.2788477 s

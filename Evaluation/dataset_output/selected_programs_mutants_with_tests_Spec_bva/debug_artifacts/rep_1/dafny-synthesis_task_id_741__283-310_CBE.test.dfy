// dafny-synthesis_task_id_741.dfy

method {:testEntry} AllCharactersSame(s: string) returns (result: bool)
  ensures result ==> forall i, j :: 0 <= i < |s| && 0 <= j < |s| ==> s[i] == s[j]
  ensures !result ==> |s| > 1 && exists i, j :: 0 <= i < |s| && 0 <= j < |s| && i != j && s[i] != s[j]
{
  return true;
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

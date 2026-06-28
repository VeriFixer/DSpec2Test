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

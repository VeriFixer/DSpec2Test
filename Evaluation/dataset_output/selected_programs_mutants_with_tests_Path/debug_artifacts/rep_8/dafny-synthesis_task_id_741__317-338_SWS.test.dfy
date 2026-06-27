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

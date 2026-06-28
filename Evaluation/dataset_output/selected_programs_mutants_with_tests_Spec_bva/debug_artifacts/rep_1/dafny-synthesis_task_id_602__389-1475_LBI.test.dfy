// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while i < |s| && !found
    invariant 0 <= i <= |s|
    invariant found == inner_found
    invariant found ==> exists ii, jj :: 0 <= ii < i && ii < jj < |s| && s[ii] == s[jj] && s[ii] == c && forall k, l :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii
    invariant !found <==> forall ii, jj :: 0 <= ii < i && ii < jj < |s| ==> s[ii] != s[jj]
  {
    break;
    var j := i + 1;
    while j < |s| && !inner_found
      invariant i < j <= |s|
      invariant inner_found ==> exists k :: i < k < |s| && s[i] == s[k] && s[i] == c
      invariant !inner_found <==> forall k :: i < k < j ==> s[i] != s[k]
    {
      if s[i] == s[j] {
        inner_found := true;
        c := s[i];
      }
      j := j + 1;
    }
    found := inner_found;
    i := i + 1;
  }
}

method {:test} Test0() {
var r0, r1 := FindFirstRepeatedChar("");
expect r0 ==> exists i, j :: 0 <= i < j < |""| && ""[i] == ""[j] && ""[i] == r1 && forall k, l :: 0 <= k < l < j && ""[k] == ""[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |""| ==> ""[i] != ""[j];
}
method {:test} Test2() {
var r0, r1 := FindFirstRepeatedChar("a");
expect r0 ==> exists i, j :: 0 <= i < j < |"a"| && "a"[i] == "a"[j] && "a"[i] == r1 && forall k, l :: 0 <= k < l < j && "a"[k] == "a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a"| ==> "a"[i] != "a"[j];
}
method {:test} Test3() {
var r0, r1 := FindFirstRepeatedChar("aa");
expect r0 ==> exists i, j :: 0 <= i < j < |"aa"| && "aa"[i] == "aa"[j] && "aa"[i] == r1 && forall k, l :: 0 <= k < l < j && "aa"[k] == "aa"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aa"| ==> "aa"[i] != "aa"[j];
}
method {:test} Test9() {
var r0, r1 := FindFirstRepeatedChar("aaaaaaaaaaaaaaaaaaaaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaa\0\0"| && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[j] && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[k] == "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaaaaaaaaaaaaaaaaaaaa\0\0"| ==> "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[i] != "aaaaaaaaaaaaaaaaaaaaaaa\0\0"[j];
}
method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("aaaaa\0\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"aaaaa\0\0"| && "aaaaa\0\0"[i] == "aaaaa\0\0"[j] && "aaaaa\0\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "aaaaa\0\0"[k] == "aaaaa\0\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"aaaaa\0\0"| ==> "aaaaa\0\0"[i] != "aaaaa\0\0"[j];
}

// REPEAT 1 - TIME: 14.7928272 s

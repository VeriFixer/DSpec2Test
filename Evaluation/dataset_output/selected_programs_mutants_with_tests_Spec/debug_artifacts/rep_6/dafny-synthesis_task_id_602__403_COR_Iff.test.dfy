// dafny-synthesis_task_id_602.dfy

method {:testEntry} FindFirstRepeatedChar(s: string) returns (found: bool, c: char)
  ensures found ==> exists i, j :: 0 <= i < j < |s| && s[i] == s[j] && s[i] == c && forall k, l :: 0 <= k < l < j && s[k] == s[l] ==> k >= i
  ensures !found ==> forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
{
  c := ' ';
  found := false;
  var inner_found := false;
  var i := 0;
  while i < |s| <==> !found
    invariant 0 <= i <= |s|
    invariant found == inner_found
    invariant found ==> exists ii, jj :: 0 <= ii < i && ii < jj < |s| && s[ii] == s[jj] && s[ii] == c && forall k, l :: 0 <= k < l < jj && s[k] == s[l] ==> k >= ii
    invariant !found <==> forall ii, jj :: 0 <= ii < i && ii < jj < |s| ==> s[ii] != s[jj]
  {
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

method {:test} Test10() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"| && "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[i] == "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[j] && "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[k] == "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"| ==> "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[i] != "\U{0003}\t\U{0007}\U{000B}aaaaaaaaaaaaaaaaa\U{0005}aa\U{0001}a"[j];
}
method {:test} Test11() {
var r0, r1 := FindFirstRepeatedChar("\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"| && "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[i] == "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[j] && "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[k] == "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"| ==> "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[i] != "\0aaa\U{0006}aaaaaa\U{0004}aaaaa\U{0002}aaaaaaa\0"[j];
}

// REPEAT 6 - TIME: 10.688754 s

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

method {:test} Test18() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"| && "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[i] == "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[j] && "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[k] == "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"| ==> "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[i] != "\U{0003}\t\U{0007}\U{000B}\raaaaaaaaaaaaaaaaa\U{0005}aaa\U{000F}\U{0001}"[j];
}
method {:test} Test19() {
var r0, r1 := FindFirstRepeatedChar("\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"| && "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[i] == "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[j] && "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[k] == "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"| ==> "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[i] != "\0\0\U{000C}\taaaaaaaaaaaaaaaaaa\U{0001}\U{0003}a\U{0005}\U{000E}\U{0007}"[j];
}

// REPEAT 10 - TIME: 17.1187582 s

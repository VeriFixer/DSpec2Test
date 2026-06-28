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

method {:test} Test26() {
var r0, r1 := FindFirstRepeatedChar("\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"| && "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[i] == "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[j] && "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[k] == "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"| ==> "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[i] != "\U{0007}aaaa\U{0017}aaaaaaaaaaaa\U{0013}a\ra\U{0003}\U{0001}\U{0015}\U{0011}\U{000F}\U{000B}\t\U{0005}"[j];
}
method {:test} Test27() {
var r0, r1 := FindFirstRepeatedChar("\0\U{0003}\U{0001}\0");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0\U{0003}\U{0001}\0"| && "\0\U{0003}\U{0001}\0"[i] == "\0\U{0003}\U{0001}\0"[j] && "\0\U{0003}\U{0001}\0"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0\U{0003}\U{0001}\0"[k] == "\0\U{0003}\U{0001}\0"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0\U{0003}\U{0001}\0"| ==> "\0\U{0003}\U{0001}\0"[i] != "\0\U{0003}\U{0001}\0"[j];
}

// REPEAT 7 - TIME: 24.1678733 s

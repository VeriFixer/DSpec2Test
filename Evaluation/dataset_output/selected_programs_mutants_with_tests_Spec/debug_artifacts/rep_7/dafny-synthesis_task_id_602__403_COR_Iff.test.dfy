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

method {:test} Test12() {
var r0, r1 := FindFirstRepeatedChar("\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"| && "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[i] == "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[j] && "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[k] == "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"| ==> "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[i] != "\U{0001}\U{000F}\t\U{0003}\U{0005}\U{000B}\raaaaaaaaaaaaaaa\U{0007}"[j];
}
method {:test} Test13() {
var r0, r1 := FindFirstRepeatedChar("\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"| && "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[i] == "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[j] && "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[k] == "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"| ==> "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[i] != "\0aaaaaaaaaaaaaaaaaaa\U{0004}\0\U{0002}\U{0008}aaaa\U{0006}"[j];
}

// REPEAT 7 - TIME: 12.5551294 s

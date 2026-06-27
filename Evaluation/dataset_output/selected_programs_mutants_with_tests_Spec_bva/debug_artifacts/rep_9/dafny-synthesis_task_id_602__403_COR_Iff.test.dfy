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

method {:test} Test30() {
var r0, r1 := FindFirstRepeatedChar("\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"| && "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[i] == "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[j] && "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[k] == "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"| ==> "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[i] != "\U{0011}\U{0007}a\U{000F}\U{0005}\U{0001}\r\t\U{000B}\U{0003}"[j];
}
method {:test} Test31() {
var r0, r1 := FindFirstRepeatedChar("a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"| && "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[i] == "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[j] && "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[k] == "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"| ==> "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[i] != "a\0\0aaaaaaa\U{0002}\U{0006}aaa\U{0004}aa\na\U{000C}aaaa\U{000E}\U{0010}\U{0008}"[j];
}

// REPEAT 9 - TIME: 21.0067352 s

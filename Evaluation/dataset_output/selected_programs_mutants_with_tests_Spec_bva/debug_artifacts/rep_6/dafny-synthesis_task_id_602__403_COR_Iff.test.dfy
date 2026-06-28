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

method {:test} Test24() {
var r0, r1 := FindFirstRepeatedChar("\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"| && "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[i] == "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[j] && "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[k] == "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"| ==> "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[i] != "\U{0003}aaaaaaaaaa\t\U{0005}aaaaa\U{000B}aaaa\U{0007}\U{000F}\r\U{0001}"[j];
}
method {:test} Test25() {
var r0, r1 := FindFirstRepeatedChar("a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"| && "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[i] == "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[j] && "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[k] == "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"| ==> "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[i] != "a\0aaaa\U{000E}\U{0004}\0a\U{0008}aa\n\U{0006}aa\U{0002}\U{000C}"[j];
}

// REPEAT 6 - TIME: 22.3068496 s

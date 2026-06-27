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

method {:test} Test32() {
var r0, r1 := FindFirstRepeatedChar("\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"| && "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[i] == "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[j] && "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[k] == "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"| ==> "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[i] != "\U{0013}\U{0011}aaaaaaaaaaaaa\raaaa\U{000F}\U{000B}\t\U{0007}\U{0005}\U{0001}\U{0003}"[j];
}
method {:test} Test33() {
var r0, r1 := FindFirstRepeatedChar("a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"| && "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[i] == "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[j] && "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[k] == "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"| ==> "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[i] != "a\0\0aa\U{0008}\naaaaaaaa\U{0002}aa\U{0010}\U{0012}\U{0004}a\U{0006}a\U{000E}\U{0014}\U{0016}\U{0018}\U{000C}"[j];
}

// REPEAT 10 - TIME: 22.2992781 s

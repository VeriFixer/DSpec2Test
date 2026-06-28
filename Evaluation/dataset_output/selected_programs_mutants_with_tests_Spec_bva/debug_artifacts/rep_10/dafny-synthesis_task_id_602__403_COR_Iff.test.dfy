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
var r0, r1 := FindFirstRepeatedChar("\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}");
expect r0 ==> exists i, j :: 0 <= i < j < |"\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"| && "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[i] == "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[j] && "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[i] == r1 && forall k, l :: 0 <= k < l < j && "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[k] == "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"| ==> "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[i] != "\U{0015}\U{0017}\U{0019}a\U{000B}\U{001D}\U{001B}aaaaaaaa\U{0011}aa\U{0013}\U{000F}\ra\ta\U{0003}\U{0007}\U{0005}\U{0001}"[j];
}
method {:test} Test33() {
var r0, r1 := FindFirstRepeatedChar("a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}");
expect r0 ==> exists i, j :: 0 <= i < j < |"a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"| && "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[i] == "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[j] && "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[i] == r1 && forall k, l :: 0 <= k < l < j && "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[k] == "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[l] ==> k >= i;
expect !r0 ==> forall i, j :: 0 <= i < j < |"a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"| ==> "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[i] != "a\0aaaa\U{0012}\U{0004}aa\0\U{0008}aaa\naa\U{000C}a\U{000E}a\U{0006}a\U{0010}\U{0002}"[j];
}

// REPEAT 10 - TIME: 30.0535604 s

// dafny-synthesis_task_id_759.dfy

method {:testEntry} IsDecimalWithTwoPrecision(s: string) returns (result: bool)
  ensures result ==> exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
  ensures !result ==> !exists i :: 0 <= i < |s| && s[i] == '.' && |s| - i - 1 == 2
{
  result := false;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant result <==> exists k :: 0 <= k < i && s[k] == '.' && |s| - k - 1 == 2
  {
    if s[i] == '.' {
      result := true;
      break;
    }
  }
}

method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a");
expect r0 ==> exists i :: 0 <= i < |"\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"| && "\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"[i] == '.' && |"\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"| && "\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"[i] == '.' && |"\U{000E}aa\U{0002}\0\U{0004}a\U{0008}aa\n\U{000C}\U{0006}a"| - i - 1 == 2;
}
method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision(".\0a");
expect r0 ==> exists i :: 0 <= i < |".\0a"| && ".\0a"[i] == '.' && |".\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".\0a"| && ".\0a"[i] == '.' && |".\0a"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 24.5347576 s

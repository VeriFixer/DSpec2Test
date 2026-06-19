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

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aa.\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}aa.\0\U{0002}"| && "\U{0004}aa.\0\U{0002}"[i] == '.' && |"\U{0004}aa.\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}aa.\0\U{0002}"| && "\U{0004}aa.\0\U{0002}"[i] == '.' && |"\U{0004}aa.\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}");
expect r0 ==> exists i :: 0 <= i < |"\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"| && "\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"[i] == '.' && |"\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"| && "\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"[i] == '.' && |"\U{000E}aa\0a\U{0004}a\U{0006}a\U{0008}a\n\U{0002}\U{000C}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 11.6667513 s

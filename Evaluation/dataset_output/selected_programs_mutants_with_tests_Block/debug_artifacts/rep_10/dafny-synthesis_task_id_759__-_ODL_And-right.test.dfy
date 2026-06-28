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

method {:test} Test18() {
var r0 := IsDecimalWithTwoPrecision("a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n");
expect r0 ==> exists i :: 0 <= i < |"a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"| && "a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"[i] == '.' && |"a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"| && "a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"[i] == '.' && |"a\0aaaa\U{0002}\U{0004}aaaa\U{0008}aa\U{0006}.\U{000C}\n"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"| && "\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"[i] == '.' && |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"| && "\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"[i] == '.' && |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\U{0004}\U{0002}"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 15.3584054 s

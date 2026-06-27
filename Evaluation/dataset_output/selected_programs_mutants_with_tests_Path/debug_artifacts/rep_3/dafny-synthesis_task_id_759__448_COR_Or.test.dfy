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
    if s[i] == '.' || |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\0aaa"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaa.\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaa.\0\U{0002}"| && "aaaaaaaaaaaaaaa.\0\U{0002}"[i] == '.' && |"aaaaaaaaaaaaaaa.\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaa.\0\U{0002}"| && "aaaaaaaaaaaaaaa.\0\U{0002}"[i] == '.' && |"aaaaaaaaaaaaaaa.\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("aa\0aaaaaaaaaa.\U{0002}a");
expect r0 ==> exists i :: 0 <= i < |"aa\0aaaaaaaaaa.\U{0002}a"| && "aa\0aaaaaaaaaa.\U{0002}a"[i] == '.' && |"aa\0aaaaaaaaaa.\U{0002}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa\0aaaaaaaaaa.\U{0002}a"| && "aa\0aaaaaaaaaa.\U{0002}a"[i] == '.' && |"aa\0aaaaaaaaaa.\U{0002}a"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 103.9220724 s

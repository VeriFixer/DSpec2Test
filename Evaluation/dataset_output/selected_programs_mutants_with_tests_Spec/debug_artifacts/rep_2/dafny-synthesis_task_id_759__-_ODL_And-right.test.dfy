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

method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaa\0aaaaaaa\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaa\0aaaaaaa\U{0002}"| && "aaaaaaaaaaaaaa\0aaaaaaa\U{0002}"[i] == '.' && |"aaaaaaaaaaaaaa\0aaaaaaa\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaa\0aaaaaaa\U{0002}"| && "aaaaaaaaaaaaaa\0aaaaaaa\U{0002}"[i] == '.' && |"aaaaaaaaaaaaaa\0aaaaaaa\U{0002}"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision(".aa");
expect r0 ==> exists i :: 0 <= i < |".aa"| && ".aa"[i] == '.' && |".aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |".aa"| && ".aa"[i] == '.' && |".aa"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 5.1816809 s

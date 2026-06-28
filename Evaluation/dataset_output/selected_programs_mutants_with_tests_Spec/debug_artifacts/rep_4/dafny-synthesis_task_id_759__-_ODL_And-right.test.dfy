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

method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaa\U{0002}aaaaaa\0a");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaa\U{0002}aaaaaa\0a"| && "aaaaaaaaaaaaaaa\U{0002}aaaaaa\0a"[i] == '.' && |"aaaaaaaaaaaaaaa\U{0002}aaaaaa\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaa\U{0002}aaaaaa\0a"| && "aaaaaaaaaaaaaaa\U{0002}aaaaaa\0a"[i] == '.' && |"aaaaaaaaaaaaaaa\U{0002}aaaaaa\0a"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaaaaaaaa\U{0001}.a\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaa\U{0001}.a\U{0005}"| && "\U{0003}aaaaaaaaaaa\U{0001}.a\U{0005}"[i] == '.' && |"\U{0003}aaaaaaaaaaa\U{0001}.a\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaa\U{0001}.a\U{0005}"| && "\U{0003}aaaaaaaaaaa\U{0001}.a\U{0005}"[i] == '.' && |"\U{0003}aaaaaaaaaaa\U{0001}.a\U{0005}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 8.2103763 s

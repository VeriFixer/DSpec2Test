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

method {:test} Test20() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| && "aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"[i] == '.' && |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| && "aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"[i] == '.' && |"aaaaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\0a"| - i - 1 == 2;
}
method {:test} Test21() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaa.a\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaa.a\U{0001}"| && "\U{0003}aaaaa.a\U{0001}"[i] == '.' && |"\U{0003}aaaaa.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaa.a\U{0001}"| && "\U{0003}aaaaa.a\U{0001}"[i] == '.' && |"\U{0003}aaaaa.a\U{0001}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 13.1628717 s

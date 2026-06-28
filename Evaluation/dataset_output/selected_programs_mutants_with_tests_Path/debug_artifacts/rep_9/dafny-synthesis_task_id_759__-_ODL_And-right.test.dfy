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

method {:test} Test24() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaa\U{0004}\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaa\U{0004}\0"| && "\U{0002}aaa\U{0004}\0"[i] == '.' && |"\U{0002}aaa\U{0004}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaa\U{0004}\0"| && "\U{0002}aaa\U{0004}\0"[i] == '.' && |"\U{0002}aaa\U{0004}\0"| - i - 1 == 2;
}
method {:test} Test25() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaa.a\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaa.a\U{0001}"| && "aaaaaaa.a\U{0001}"[i] == '.' && |"aaaaaaa.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaa.a\U{0001}"| && "aaaaaaa.a\U{0001}"[i] == '.' && |"aaaaaaa.a\U{0001}"| - i - 1 == 2;
}
method {:test} Test26() {
var r0 := IsDecimalWithTwoPrecision("aaaaaa.a\U{0001}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaa.a\U{0001}"| && "aaaaaa.a\U{0001}"[i] == '.' && |"aaaaaa.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaa.a\U{0001}"| && "aaaaaa.a\U{0001}"[i] == '.' && |"aaaaaa.a\U{0001}"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 358.5306782 s

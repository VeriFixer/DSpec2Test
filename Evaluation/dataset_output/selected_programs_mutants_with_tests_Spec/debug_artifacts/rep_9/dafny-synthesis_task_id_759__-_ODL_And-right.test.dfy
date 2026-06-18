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

method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaa\0aaaa\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaa\0aaaa\U{0004}\U{0002}"| && "\U{0006}aaa\0aaaa\U{0004}\U{0002}"[i] == '.' && |"\U{0006}aaa\0aaaa\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaa\0aaaa\U{0004}\U{0002}"| && "\U{0006}aaa\0aaaa\U{0004}\U{0002}"[i] == '.' && |"\U{0006}aaa\0aaaa\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"| && "\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"[i] == '.' && |"\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"| && "\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"[i] == '.' && |"\U{000B}aaaaa\U{0005}aa\U{0001}\ta\U{0003}a\U{0007}.aa"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 13.8819187 s

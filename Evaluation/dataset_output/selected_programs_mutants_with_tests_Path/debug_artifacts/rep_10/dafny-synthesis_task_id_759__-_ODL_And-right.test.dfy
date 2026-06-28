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

method {:test} Test27() {
var r0 := IsDecimalWithTwoPrecision("\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"| && "\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"[i] == '.' && |"\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"| && "\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"[i] == '.' && |"\U{0008}aaaaaa\U{0004}aa\U{0006}aaaaaaaaaaa\0\U{0002}"| - i - 1 == 2;
}
method {:test} Test28() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaa.\U{0002}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
}

// REPEAT 10 - TIME: 412.1149416 s

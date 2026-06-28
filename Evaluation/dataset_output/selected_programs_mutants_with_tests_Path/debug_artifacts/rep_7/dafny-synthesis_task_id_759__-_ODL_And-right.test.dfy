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
var r0 := IsDecimalWithTwoPrecision("\U{0006}a\0a\U{0004}\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}a\0a\U{0004}\U{0002}"| && "\U{0006}a\0a\U{0004}\U{0002}"[i] == '.' && |"\U{0006}a\0a\U{0004}\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}a\0a\U{0004}\U{0002}"| && "\U{0006}a\0a\U{0004}\U{0002}"[i] == '.' && |"\U{0006}a\0a\U{0004}\U{0002}"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"| && "aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"[i] == '.' && |"aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"| && "aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"[i] == '.' && |"aaaaaaaaaaaaaaaa\U{0002}a.\U{0004}\0"| - i - 1 == 2;
}
method {:test} Test20() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"| && "aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"[i] == '.' && |"aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"| && "aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"[i] == '.' && |"aaaaaaaaaaaaaa\U{0004}aa\U{0002}.\0a"| - i - 1 == 2;
}

// REPEAT 7 - TIME: 248.0897013 s

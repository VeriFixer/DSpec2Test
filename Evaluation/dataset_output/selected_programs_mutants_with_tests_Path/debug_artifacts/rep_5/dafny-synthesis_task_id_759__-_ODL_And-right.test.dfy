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

method {:test} Test12() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"| && "\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"[i] == '.' && |"\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"| && "\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"[i] == '.' && |"\0aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\U{0004}\U{0006}"| - i - 1 == 2;
}
method {:test} Test13() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"| && "aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"[i] == '.' && |"aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"| && "aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"[i] == '.' && |"aaaaaaaaaaaaaaaa\0\U{0002}\U{0004}\U{0006}aaaaaa.a\U{0008}"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 187.9542148 s

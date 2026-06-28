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

method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"| && "\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"[i] == '.' && |"\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"| && "\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"[i] == '.' && |"\0aaaaaa\U{0002}aaaaa\U{0006}.\U{0004}\U{0008}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("\0a\U{0002}");
expect r0 ==> exists i :: 0 <= i < |"\0a\U{0002}"| && "\0a\U{0002}"[i] == '.' && |"\0a\U{0002}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0a\U{0002}"| && "\0a\U{0002}"[i] == '.' && |"\0a\U{0002}"| - i - 1 == 2;
}

// REPEAT 8 - TIME: 12.6007549 s

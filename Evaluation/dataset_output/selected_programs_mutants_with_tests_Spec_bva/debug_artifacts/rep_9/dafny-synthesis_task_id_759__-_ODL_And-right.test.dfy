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

method {:test} Test28() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"| && "\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"[i] == '.' && |"\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"| && "\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"[i] == '.' && |"\U{0002}aaaaaaaaaaaa\U{0006}a\n\0aaa\U{0004}\U{000C}\U{0008}"| - i - 1 == 2;
}
method {:test} Test29() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"| && "\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"[i] == '.' && |"\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"| && "\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"[i] == '.' && |"\U{0003}aaaaaaaaaaaaa\U{0001}\ta\U{000B}\U{0007}a.\r\U{0005}"| - i - 1 == 2;
}

// REPEAT 9 - TIME: 18.6935908 s

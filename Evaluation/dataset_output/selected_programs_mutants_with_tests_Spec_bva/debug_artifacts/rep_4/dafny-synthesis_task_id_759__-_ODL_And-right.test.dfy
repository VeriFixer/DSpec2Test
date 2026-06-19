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
var r0 := IsDecimalWithTwoPrecision("\U{0002}a\0");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}a\0"| && "\U{0002}a\0"[i] == '.' && |"\U{0002}a\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}a\0"| && "\U{0002}a\0"[i] == '.' && |"\U{0002}a\0"| - i - 1 == 2;
}
method {:test} Test19() {
var r0 := IsDecimalWithTwoPrecision("\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}");
expect r0 ==> exists i :: 0 <= i < |"\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"| && "\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"[i] == '.' && |"\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"| && "\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"[i] == '.' && |"\U{0003}aaaaa\U{0001}aaaaaa.\U{0005}\U{0007}"| - i - 1 == 2;
}

// REPEAT 4 - TIME: 13.2367094 s

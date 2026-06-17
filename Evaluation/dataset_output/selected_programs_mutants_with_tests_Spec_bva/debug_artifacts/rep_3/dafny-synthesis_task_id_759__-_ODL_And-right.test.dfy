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
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na");
expect r0 ==> exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| && "\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"[i] == '.' && |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| && "\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"[i] == '.' && |"\U{0006}aaaaaaaaaaa\U{0004}aaaaaa\0aaaaaaaaaa\U{0002}aaaaaaaaaa\U{0008}\na"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}\U{0001}.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0005}\U{0001}.\U{0003}a"| && "\U{0005}\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0005}\U{0001}.\U{0003}a"| && "\U{0005}\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}.\U{0003}a"| - i - 1 == 2;
}

// REPEAT 3 - TIME: 11.1470841 s

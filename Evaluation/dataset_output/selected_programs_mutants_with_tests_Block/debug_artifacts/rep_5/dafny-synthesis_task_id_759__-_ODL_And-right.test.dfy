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

method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}.\U{0003}a");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}.\U{0003}a"| && "\U{0001}.\U{0003}a"[i] == '.' && |"\U{0001}.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}.\U{0003}a"| && "\U{0001}.\U{0003}a"[i] == '.' && |"\U{0001}.\U{0003}a"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 9.1169154 s

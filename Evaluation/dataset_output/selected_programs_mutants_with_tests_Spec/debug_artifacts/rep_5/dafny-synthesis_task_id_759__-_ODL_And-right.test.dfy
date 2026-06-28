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
var r0 := IsDecimalWithTwoPrecision("\0");
expect r0 ==> exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaa.\0a");
expect r0 ==> exists i :: 0 <= i < |"\U{0002}aaaaa.\0a"| && "\U{0002}aaaaa.\0a"[i] == '.' && |"\U{0002}aaaaa.\0a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0002}aaaaa.\0a"| && "\U{0002}aaaaa.\0a"[i] == '.' && |"\U{0002}aaaaa.\0a"| - i - 1 == 2;
}

// REPEAT 5 - TIME: 9.8319232 s

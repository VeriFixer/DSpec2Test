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

method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("\U{0001}aaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\U{0001}aaa.aa"| && "\U{0001}aaa.aa"[i] == '.' && |"\U{0001}aaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\U{0001}aaa.aa"| && "\U{0001}aaa.aa"[i] == '.' && |"\U{0001}aaa.aa"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("aaaaa\0");
expect r0 ==> exists i :: 0 <= i < |"aaaaa\0"| && "aaaaa\0"[i] == '.' && |"aaaaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaa\0"| && "aaaaa\0"[i] == '.' && |"aaaaa\0"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 4.1491531 s

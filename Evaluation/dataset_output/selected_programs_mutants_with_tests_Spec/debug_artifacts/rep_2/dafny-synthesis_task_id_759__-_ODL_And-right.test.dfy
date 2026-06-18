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
var r0 := IsDecimalWithTwoPrecision("aaa\0");
expect r0 ==> exists i :: 0 <= i < |"aaa\0"| && "aaa\0"[i] == '.' && |"aaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaa\0"| && "aaa\0"[i] == '.' && |"aaa\0"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("\0aaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"\0aaaaaaaaa.aa"| && "\0aaaaaaaaa.aa"[i] == '.' && |"\0aaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"\0aaaaaaaaa.aa"| && "\0aaaaaaaaa.aa"[i] == '.' && |"\0aaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 2 - TIME: 4.8951095 s

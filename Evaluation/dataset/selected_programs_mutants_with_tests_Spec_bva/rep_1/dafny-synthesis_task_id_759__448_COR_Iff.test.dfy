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
    if s[i] == '.' <==> |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}

method {:test} Test0() {
var r0 := IsDecimalWithTwoPrecision("");
expect r0 ==> exists i :: 0 <= i < |""| && ""[i] == '.' && |""| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |""| && ""[i] == '.' && |""| - i - 1 == 2;
}
method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("a");
expect r0 ==> exists i :: 0 <= i < |"a"| && "a"[i] == '.' && |"a"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"a"| && "a"[i] == '.' && |"a"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("aa");
expect r0 ==> exists i :: 0 <= i < |"aa"| && "aa"[i] == '.' && |"aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aa"| && "aa"[i] == '.' && |"aa"| - i - 1 == 2;
}
method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaa.aa"| && "aaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaa.aa"| && "aaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test10() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}

// REPEAT 1 - TIME: 8.6987499 s

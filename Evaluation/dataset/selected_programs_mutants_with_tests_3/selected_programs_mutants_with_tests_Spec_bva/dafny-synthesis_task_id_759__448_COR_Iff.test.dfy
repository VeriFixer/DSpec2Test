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
method {:test} Test14() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}");
expect r0 ==> exists i: int {:trigger "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"[i]} :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"[i]} :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0\U{0004}"| - i - 1 == 2;
}
method {:test} Test15() {
var r0 := IsDecimalWithTwoPrecision("a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}");
expect r0 ==> exists i: int {:trigger "a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}"[i]} :: 0 <= i < |"a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}"| && "a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}"[i] == '.' && |"a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}"[i]} :: 0 <= i < |"a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}"| && "a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}"[i] == '.' && |"a\U{0001}aaaaaaaaaa\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0005}\U{0007}"| - i - 1 == 2;
}
method {:test} Test16() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}a\0");
expect r0 ==> exists i: int {:trigger "\U{0002}a\0"[i]} :: 0 <= i < |"\U{0002}a\0"| && "\U{0002}a\0"[i] == '.' && |"\U{0002}a\0"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "\U{0002}a\0"[i]} :: 0 <= i < |"\U{0002}a\0"| && "\U{0002}a\0"[i] == '.' && |"\U{0002}a\0"| - i - 1 == 2;
}
method {:test} Test17() {
var r0 := IsDecimalWithTwoPrecision("\U{0005}\U{0001}.\U{0003}a");
expect r0 ==> exists i: int {:trigger "\U{0005}\U{0001}.\U{0003}a"[i]} :: 0 <= i < |"\U{0005}\U{0001}.\U{0003}a"| && "\U{0005}\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}.\U{0003}a"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "\U{0005}\U{0001}.\U{0003}a"[i]} :: 0 <= i < |"\U{0005}\U{0001}.\U{0003}a"| && "\U{0005}\U{0001}.\U{0003}a"[i] == '.' && |"\U{0005}\U{0001}.\U{0003}a"| - i - 1 == 2;
}

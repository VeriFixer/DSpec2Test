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
    if s[i] == '.' ==> |s| - i - 1 == 2 {
      result := true;
      break;
    }
  }
}

method {:test} Test0() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.aa"| - i - 1 == 2;
}
method {:test} Test1() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 ==> exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa"| - i - 1 == 2;
}
method {:test} Test2() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}");
expect r0 ==> exists i: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}"[i]} :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}"[i]} :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}.a\U{0001}"| - i - 1 == 2;
}
method {:test} Test3() {
var r0 := IsDecimalWithTwoPrecision("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 ==> exists i: int {:trigger "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]} :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i]} :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| && "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"[i] == '.' && |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| - i - 1 == 2;
}
method {:test} Test4() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}");
expect r0 ==> exists i: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}"[i]} :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}"[i]} :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0001}\U{0003}"| - i - 1 == 2;
}
method {:test} Test5() {
var r0 := IsDecimalWithTwoPrecision("\0");
expect r0 ==> exists i: int {:trigger "\0"[i]} :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "\0"[i]} :: 0 <= i < |"\0"| && "\0"[i] == '.' && |"\0"| - i - 1 == 2;
}
method {:test} Test6() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0");
expect r0 ==> exists i: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i]} :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i]} :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.\U{0002}\0"| - i - 1 == 2;
}
method {:test} Test7() {
var r0 := IsDecimalWithTwoPrecision("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa");
expect r0 ==> exists i: int {:trigger "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa"[i]} :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa"| && "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa"[i] == '.' && |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa"[i]} :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa"| && "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa"[i] == '.' && |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\0aa"| - i - 1 == 2;
}
method {:test} Test8() {
var r0 := IsDecimalWithTwoPrecision("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a");
expect r0 ==> exists i: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a"[i]} :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a"[i]} :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a"| && "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a"[i] == '.' && |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0001}a\U{0003}.\U{0005}a"| - i - 1 == 2;
}
method {:test} Test9() {
var r0 := IsDecimalWithTwoPrecision("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}");
expect r0 ==> exists i: int {:trigger "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[i]} :: 0 <= i < |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| && "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[i] == '.' && |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| - i - 1 == 2;
expect !r0 ==> !exists i: int {:trigger "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[i]} :: 0 <= i < |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| && "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"[i] == '.' && |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0aa\U{0002}\U{0004}"| - i - 1 == 2;
}

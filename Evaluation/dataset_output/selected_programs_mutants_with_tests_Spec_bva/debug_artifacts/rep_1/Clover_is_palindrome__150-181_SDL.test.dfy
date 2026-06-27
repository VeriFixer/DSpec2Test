// Clover_is_palindrome.dfy

method {:testEntry} IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1]
{
  var i := 0;
  var j := |x| - 1;
  result := true;
  while i < j
    invariant 0 <= i <= j + 1 && 0 <= j < |x|
    invariant i + j == |x| - 1
    invariant forall k :: 0 <= k < i ==> x[k] == x[|x| - k - 1]
  {
    if x[i] != x[j] {
      result := false;
      return;
    }
    i := i + 1;
    j := j - 1;
  }
}

method {:test} Test0() {
var r0 := IsPalindrome("");
expect r0 <==> forall i :: 0 <= i < |""| ==> ""[i] == ""[|""| - i - 1];
}
method {:test} Test2() {
var r0 := IsPalindrome("a");
expect r0 <==> forall i :: 0 <= i < |"a"| ==> "a"[i] == "a"[|"a"| - i - 1];
}
method {:test} Test3() {
var r0 := IsPalindrome("aa");
expect r0 <==> forall i :: 0 <= i < |"aa"| ==> "aa"[i] == "aa"[|"aa"| - i - 1];
}
method {:test} Test8() {
var r0 := IsPalindrome("aa\U{0002}aaaaa\0aa");
expect r0 <==> forall i :: 0 <= i < |"aa\U{0002}aaaaa\0aa"| ==> "aa\U{0002}aaaaa\0aa"[i] == "aa\U{0002}aaaaa\0aa"[|"aa\U{0002}aaaaa\0aa"| - i - 1];
}
method {:test} Test9() {
var r0 := IsPalindrome("\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0002}"| ==> "\0\U{0002}"[i] == "\0\U{0002}"[|"\0\U{0002}"| - i - 1];
}
method {:test} Test10() {
var r0 := IsPalindrome("aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa");
expect r0 <==> forall i :: 0 <= i < |"aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa"| ==> "aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa"[i] == "aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa"[|"aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa"| - i - 1];
}
method {:test} Test12() {
var r0 := IsPalindrome("\U{0002}aaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaa\0"| ==> "\U{0002}aaaaaaa\0"[i] == "\U{0002}aaaaaaa\0"[|"\U{0002}aaaaaaa\0"| - i - 1];
}
method {:test} Test13() {
var r0 := IsPalindrome("aa\U{0002}aaa\0aa");
expect r0 <==> forall i :: 0 <= i < |"aa\U{0002}aaa\0aa"| ==> "aa\U{0002}aaa\0aa"[i] == "aa\U{0002}aaa\0aa"[|"aa\U{0002}aaa\0aa"| - i - 1];
}

// REPEAT 1 - TIME: 9.0194992 s

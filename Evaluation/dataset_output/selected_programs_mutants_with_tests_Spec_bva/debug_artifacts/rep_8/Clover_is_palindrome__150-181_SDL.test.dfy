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

method {:test} Test26() {
var r0 := IsPalindrome("a\0\0aaaaa\0aaa\0a\0\0aa\0");
expect r0 <==> forall i :: 0 <= i < |"a\0\0aaaaa\0aaa\0a\0\0aa\0"| ==> "a\0\0aaaaa\0aaa\0a\0\0aa\0"[i] == "a\0\0aaaaa\0aaa\0a\0\0aa\0"[|"a\0\0aaaaa\0aaa\0a\0\0aa\0"| - i - 1];
}
method {:test} Test27() {
var r0 := IsPalindrome("\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}");
expect r0 <==> forall i :: 0 <= i < |"\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}"| ==> "\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}"[i] == "\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}"[|"\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}"| - i - 1];
}

// REPEAT 8 - TIME: 27.5096495 s

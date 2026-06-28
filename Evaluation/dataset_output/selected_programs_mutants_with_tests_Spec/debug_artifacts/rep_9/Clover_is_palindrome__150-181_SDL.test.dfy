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

method {:test} Test16() {
var r0 := IsPalindrome("\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] == "\0a"[|"\0a"| - i - 1];
}
method {:test} Test17() {
var r0 := IsPalindrome("a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a");
expect r0 <==> forall i :: 0 <= i < |"a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a"| ==> "a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a"[i] == "a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a"[|"a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a"| - i - 1];
}

// REPEAT 9 - TIME: 14.3127529 s

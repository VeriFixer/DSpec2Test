// Clover_is_palindrome.dfy

method {:testEntry} IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1]
{
  if false {
    return true;
  }
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
var r0 := IsPalindrome("\0aa\U{0002}aaaaaa\0\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaa\0\0a"| ==> "\0aa\U{0002}aaaaaa\0\0a"[i] == "\0aa\U{0002}aaaaaa\0\0a"[|"\0aa\U{0002}aaaaaa\0\0a"| - i - 1];
}
method {:test} Test17() {
var r0 := IsPalindrome("\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a"| ==> "\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a"[i] == "\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a"[|"\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a"| - i - 1];
}

// REPEAT 3 - TIME: 17.885548 s

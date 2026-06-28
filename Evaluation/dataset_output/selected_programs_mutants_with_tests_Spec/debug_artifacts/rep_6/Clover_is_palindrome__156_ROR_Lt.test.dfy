// Clover_is_palindrome.dfy

method {:testEntry} IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1]
{
  if |x| < 0 {
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

method {:test} Test10() {
var r0 := IsPalindrome("\0\0aaaaaa\0aa\0aaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0\0aaaaaa\0aa\0aaaa\0a"| ==> "\0\0aaaaaa\0aa\0aaaa\0a"[i] == "\0\0aaaaaa\0aa\0aaaa\0a"[|"\0\0aaaaaa\0aa\0aaaa\0a"| - i - 1];
}
method {:test} Test11() {
var r0 := IsPalindrome("\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa"| ==> "\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa"[i] == "\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa"[|"\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa"| - i - 1];
}

// REPEAT 6 - TIME: 10.7079609 s

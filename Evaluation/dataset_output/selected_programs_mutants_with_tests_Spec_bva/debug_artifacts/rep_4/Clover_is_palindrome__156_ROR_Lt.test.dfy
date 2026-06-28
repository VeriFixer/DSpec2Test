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

method {:test} Test18() {
var r0 := IsPalindrome("\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a"| ==> "\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a"[i] == "\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a"[|"\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a"| - i - 1];
}
method {:test} Test19() {
var r0 := IsPalindrome("\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0"[i] == "\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0"[|"\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0"| - i - 1];
}

// REPEAT 4 - TIME: 19.8975657 s

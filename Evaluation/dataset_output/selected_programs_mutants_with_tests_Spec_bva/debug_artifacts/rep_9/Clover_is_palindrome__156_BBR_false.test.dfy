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

method {:test} Test28() {
var r0 := IsPalindrome("\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a"| ==> "\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a"[i] == "\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a"[|"\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a"| - i - 1];
}
method {:test} Test29() {
var r0 := IsPalindrome("\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a");
expect r0 <==> forall i :: 0 <= i < |"\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a"| ==> "\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a"[i] == "\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a"[|"\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a"| - i - 1];
}

// REPEAT 9 - TIME: 16.6845595 s

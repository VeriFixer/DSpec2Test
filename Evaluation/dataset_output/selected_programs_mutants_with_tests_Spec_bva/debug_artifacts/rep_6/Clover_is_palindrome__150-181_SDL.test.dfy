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

method {:test} Test22() {
var r0 := IsPalindrome("\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a");
expect r0 <==> forall i :: 0 <= i < |"\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a"| ==> "\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a"[i] == "\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a"[|"\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a"| - i - 1];
}
method {:test} Test23() {
var r0 := IsPalindrome("\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n");
expect r0 <==> forall i :: 0 <= i < |"\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n"| ==> "\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n"[i] == "\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n"[|"\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n"| - i - 1];
}

// REPEAT 6 - TIME: 23.5892715 s

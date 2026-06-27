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

method {:test} Test26() {
var r0 := IsPalindrome("\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a"| ==> "\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a"[i] == "\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a"[|"\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a"| - i - 1];
}
method {:test} Test27() {
var r0 := IsPalindrome("\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a"| ==> "\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a"[i] == "\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a"[|"\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a"| - i - 1];
}

// REPEAT 8 - TIME: 15.7315768 s

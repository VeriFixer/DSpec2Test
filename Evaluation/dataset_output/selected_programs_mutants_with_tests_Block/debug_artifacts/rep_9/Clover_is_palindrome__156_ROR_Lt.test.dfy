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

method {:test} Test24() {
var r0 := IsPalindrome("\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0"| ==> "\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0"[i] == "\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0"[|"\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0"| - i - 1];
}
method {:test} Test25() {
var r0 := IsPalindrome("\0\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0004}\U{0002}"| ==> "\0\U{0004}\U{0002}"[i] == "\0\U{0004}\U{0002}"[|"\0\U{0004}\U{0002}"| - i - 1];
}
method {:test} Test26() {
var r0 := IsPalindrome("\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0"| ==> "\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0"[i] == "\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0"[|"\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0"| - i - 1];
}

// REPEAT 9 - TIME: 15.4333324 s

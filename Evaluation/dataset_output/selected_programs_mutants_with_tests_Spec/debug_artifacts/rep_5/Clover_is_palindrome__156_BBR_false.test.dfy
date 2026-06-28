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

method {:test} Test8() {
var r0 := IsPalindrome("\0a\U{0002}aaaaaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\U{0002}aaaaaaaaa\0a"| ==> "\0a\U{0002}aaaaaaaaa\0a"[i] == "\0a\U{0002}aaaaaaaaa\0a"[|"\0a\U{0002}aaaaaaaaa\0a"| - i - 1];
}
method {:test} Test9() {
var r0 := IsPalindrome("\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}"| ==> "\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}"[i] == "\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}"[|"\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}"| - i - 1];
}

// REPEAT 5 - TIME: 9.5828188 s

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

method {:test} Test14() {
var r0 := IsPalindrome("\0\0aaaaaa\0aa\0aa\0a\0aaa");
expect r0 <==> forall i :: 0 <= i < |"\0\0aaaaaa\0aa\0aa\0a\0aaa"| ==> "\0\0aaaaaa\0aa\0aa\0a\0aaa"[i] == "\0\0aaaaaa\0aa\0aa\0a\0aaa"[|"\0\0aaaaaa\0aa\0aa\0a\0aaa"| - i - 1];
}
method {:test} Test15() {
var r0 := IsPalindrome("\U{0006}\0\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0\U{0002}\U{0004}"| ==> "\U{0006}\0\U{0002}\U{0004}"[i] == "\U{0006}\0\U{0002}\U{0004}"[|"\U{0006}\0\U{0002}\U{0004}"| - i - 1];
}

// REPEAT 8 - TIME: 12.986437 s

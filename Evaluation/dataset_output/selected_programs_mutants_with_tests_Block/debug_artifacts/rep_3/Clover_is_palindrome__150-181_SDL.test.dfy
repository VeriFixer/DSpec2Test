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

method {:test} Test6() {
var r0 := IsPalindrome("\0\0");
expect r0 <==> forall i :: 0 <= i < |"\0\0"| ==> "\0\0"[i] == "\0\0"[|"\0\0"| - i - 1];
}
method {:test} Test7() {
var r0 := IsPalindrome("\0\U{0004}aaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0004}aaaaaaaaaaaaaaa\U{0002}"| ==> "\0\U{0004}aaaaaaaaaaaaaaa\U{0002}"[i] == "\0\U{0004}aaaaaaaaaaaaaaa\U{0002}"[|"\0\U{0004}aaaaaaaaaaaaaaa\U{0002}"| - i - 1];
}
method {:test} Test8() {
var r0 := IsPalindrome("\0aaaaaa\U{0004}a\U{0002}aaaaa\U{0006}\0");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaa\U{0004}a\U{0002}aaaaa\U{0006}\0"| ==> "\0aaaaaa\U{0004}a\U{0002}aaaaa\U{0006}\0"[i] == "\0aaaaaa\U{0004}a\U{0002}aaaaa\U{0006}\0"[|"\0aaaaaa\U{0004}a\U{0002}aaaaa\U{0006}\0"| - i - 1];
}

// REPEAT 3 - TIME: 5.9836158 s

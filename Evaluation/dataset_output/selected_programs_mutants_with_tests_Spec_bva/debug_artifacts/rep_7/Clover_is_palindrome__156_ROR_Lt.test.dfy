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
var r0 := IsPalindrome("a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0"| ==> "a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0"[i] == "a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0"[|"a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0"| - i - 1];
}
method {:test} Test25() {
var r0 := IsPalindrome("\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}"| ==> "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}"[i] == "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}"[|"\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}"| - i - 1];
}

// REPEAT 7 - TIME: 25.6409536 s

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

method {:test} Test6() {
var r0 := IsPalindrome("a\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"a\U{0002}\0"| ==> "a\U{0002}\0"[i] == "a\U{0002}\0"[|"a\U{0002}\0"| - i - 1];
}
method {:test} Test7() {
var r0 := IsPalindrome("\U{0004}\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0\U{0002}"| ==> "\U{0004}\0\U{0002}"[i] == "\U{0004}\0\U{0002}"[|"\U{0004}\0\U{0002}"| - i - 1];
}

// REPEAT 4 - TIME: 8.2026961 s

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

method {:test} Test18() {
var r0 := IsPalindrome("\0\0\0");
expect r0 <==> forall i :: 0 <= i < |"\0\0\0"| ==> "\0\0\0"[i] == "\0\0\0"[|"\0\0\0"| - i - 1];
}
method {:test} Test19() {
var r0 := IsPalindrome("\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}"| ==> "\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}"[i] == "\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}"[|"\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}"| - i - 1];
}

// REPEAT 10 - TIME: 15.8060666 s

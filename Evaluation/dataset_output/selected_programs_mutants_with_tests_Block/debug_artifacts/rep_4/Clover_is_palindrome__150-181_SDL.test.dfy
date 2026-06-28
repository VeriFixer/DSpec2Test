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

method {:test} Test9() {
var r0 := IsPalindrome("\U{0004}\0\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0\U{0002}\U{0004}"| ==> "\U{0004}\0\U{0002}\U{0004}"[i] == "\U{0004}\0\U{0002}\U{0004}"[|"\U{0004}\0\U{0002}\U{0004}"| - i - 1];
}
method {:test} Test10() {
var r0 := IsPalindrome("\0\U{0004}aaaaaaaaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0004}aaaaaaaaaaaaa\U{0002}"| ==> "\0\U{0004}aaaaaaaaaaaaa\U{0002}"[i] == "\0\U{0004}aaaaaaaaaaaaa\U{0002}"[|"\0\U{0004}aaaaaaaaaaaaa\U{0002}"| - i - 1];
}
method {:test} Test11() {
var r0 := IsPalindrome("\U{0008}aaaaaaaaaaaaaa\0a\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}aaaaaaaaaaaaaa\0a\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}"| ==> "\U{0008}aaaaaaaaaaaaaa\0a\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}"[i] == "\U{0008}aaaaaaaaaaaaaa\0a\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}"[|"\U{0008}aaaaaaaaaaaaaa\0a\U{0002}\U{0004}aaaaaa\U{0006}\U{0008}"| - i - 1];
}

// REPEAT 4 - TIME: 7.5687007 s

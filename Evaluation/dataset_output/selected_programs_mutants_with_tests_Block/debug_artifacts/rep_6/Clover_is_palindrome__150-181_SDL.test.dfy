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

method {:test} Test15() {
var r0 := IsPalindrome("\U{000C}aaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}aa\0aaa\U{0008}a\n\U{000C}");
expect r0 <==> forall i :: 0 <= i < |"\U{000C}aaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}aa\0aaa\U{0008}a\n\U{000C}"| ==> "\U{000C}aaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}aa\0aaa\U{0008}a\n\U{000C}"[i] == "\U{000C}aaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}aa\0aaa\U{0008}a\n\U{000C}"[|"\U{000C}aaaaaaaaaaaaaa\U{0004}a\U{0002}\U{0006}aa\0aaa\U{0008}a\n\U{000C}"| - i - 1];
}
method {:test} Test16() {
var r0 := IsPalindrome("\0\U{0004}\U{0006}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0004}\U{0006}\U{0002}"| ==> "\0\U{0004}\U{0006}\U{0002}"[i] == "\0\U{0004}\U{0006}\U{0002}"[|"\0\U{0004}\U{0006}\U{0002}"| - i - 1];
}
method {:test} Test17() {
var r0 := IsPalindrome("\0\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0002}\0"| ==> "\0\U{0002}\0"[i] == "\0\U{0002}\0"[|"\0\U{0002}\0"| - i - 1];
}

// REPEAT 6 - TIME: 10.8618504 s

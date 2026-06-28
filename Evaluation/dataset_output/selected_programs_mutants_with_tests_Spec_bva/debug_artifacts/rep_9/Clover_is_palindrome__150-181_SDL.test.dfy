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

method {:test} Test28() {
var r0 := IsPalindrome("\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a"| ==> "\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a"[i] == "\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a"[|"\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a"| - i - 1];
}
method {:test} Test29() {
var r0 := IsPalindrome("\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}");
expect r0 <==> forall i :: 0 <= i < |"\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}"| ==> "\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}"[i] == "\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}"[|"\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}"| - i - 1];
}

// REPEAT 9 - TIME: 29.3311426 s

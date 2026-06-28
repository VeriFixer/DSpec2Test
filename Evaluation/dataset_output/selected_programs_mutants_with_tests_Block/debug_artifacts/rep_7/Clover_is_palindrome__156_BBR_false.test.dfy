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

method {:test} Test18() {
var r0 := IsPalindrome("\0aaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}\U{0002}\n\U{000E}a\U{000C}aa\U{0010}aa\U{0012}\0");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}\U{0002}\n\U{000E}a\U{000C}aa\U{0010}aa\U{0012}\0"| ==> "\0aaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}\U{0002}\n\U{000E}a\U{000C}aa\U{0010}aa\U{0012}\0"[i] == "\0aaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}\U{0002}\n\U{000E}a\U{000C}aa\U{0010}aa\U{0012}\0"[|"\0aaaaaaaaaaaaaa\U{0004}\U{0006}\U{0008}\U{0002}\n\U{000E}a\U{000C}aa\U{0010}aa\U{0012}\0"| - i - 1];
}
method {:test} Test19() {
var r0 := IsPalindrome("\0\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0004}\U{0002}"| ==> "\0\U{0004}\U{0002}"[i] == "\0\U{0004}\U{0002}"[|"\0\U{0004}\U{0002}"| - i - 1];
}
method {:test} Test20() {
var r0 := IsPalindrome("\U{0008}aa\0aaaaaaaaaaaa\U{0002}aa\U{0004}\U{0006}aaaaaa\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}aa\0aaaaaaaaaaaa\U{0002}aa\U{0004}\U{0006}aaaaaa\U{0008}"| ==> "\U{0008}aa\0aaaaaaaaaaaa\U{0002}aa\U{0004}\U{0006}aaaaaa\U{0008}"[i] == "\U{0008}aa\0aaaaaaaaaaaa\U{0002}aa\U{0004}\U{0006}aaaaaa\U{0008}"[|"\U{0008}aa\0aaaaaaaaaaaa\U{0002}aa\U{0004}\U{0006}aaaaaa\U{0008}"| - i - 1];
}

// REPEAT 7 - TIME: 12.6799653 s

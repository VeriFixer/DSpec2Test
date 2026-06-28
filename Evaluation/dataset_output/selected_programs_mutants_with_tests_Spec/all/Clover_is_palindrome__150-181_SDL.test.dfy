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


method {:test} Test0() {
var r0 := IsPalindrome("");
expect r0 <==> forall i :: 0 <= i < |""| ==> ""[i] == ""[|""| - i - 1];
}
method {:test} Test1() {
var r0 := IsPalindrome("aa\U{0002}aaaaa\0aa");
expect r0 <==> forall i :: 0 <= i < |"aa\U{0002}aaaaa\0aa"| ==> "aa\U{0002}aaaaa\0aa"[i] == "aa\U{0002}aaaaa\0aa"[|"aa\U{0002}aaaaa\0aa"| - i - 1];
}

// REPEAT 1 - TIME: 3.6420506 s

method {:test} Test2() {
var r0 := IsPalindrome("\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] == "\0a"[|"\0a"| - i - 1];
}
method {:test} Test3() {
var r0 := IsPalindrome("\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0002}"| ==> "\0\U{0002}"[i] == "\0\U{0002}"[|"\0\U{0002}"| - i - 1];
}

// REPEAT 2 - TIME: 5.0252417 s

method {:test} Test4() {
var r0 := IsPalindrome("\0");
expect r0 <==> forall i :: 0 <= i < |"\0"| ==> "\0"[i] == "\0"[|"\0"| - i - 1];
}
method {:test} Test5() {
var r0 := IsPalindrome("\U{0002}aaaaaaaa\U{0004}aaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaaa\U{0004}aaaaaa\0"| ==> "\U{0002}aaaaaaaa\U{0004}aaaaaa\0"[i] == "\U{0002}aaaaaaaa\U{0004}aaaaaa\0"[|"\U{0002}aaaaaaaa\U{0004}aaaaaa\0"| - i - 1];
}

// REPEAT 3 - TIME: 6.6677215 s

method {:test} Test6() {
var r0 := IsPalindrome("a\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"a\U{0002}\0"| ==> "a\U{0002}\0"[i] == "a\U{0002}\0"[|"a\U{0002}\0"| - i - 1];
}
method {:test} Test7() {
var r0 := IsPalindrome("\U{0004}\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0\U{0002}"| ==> "\U{0004}\0\U{0002}"[i] == "\U{0004}\0\U{0002}"[|"\U{0004}\0\U{0002}"| - i - 1];
}

// REPEAT 4 - TIME: 8.2026961 s

method {:test} Test8() {
var r0 := IsPalindrome("\0a\U{0002}aaaaaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\U{0002}aaaaaaaaa\0a"| ==> "\0a\U{0002}aaaaaaaaa\0a"[i] == "\0a\U{0002}aaaaaaaaa\0a"[|"\0a\U{0002}aaaaaaaaa\0a"| - i - 1];
}
method {:test} Test9() {
var r0 := IsPalindrome("\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}"| ==> "\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}"[i] == "\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}"[|"\U{0006}\0aaaaaaa\U{0004}aaaaaa\U{0002}"| - i - 1];
}

// REPEAT 5 - TIME: 9.5828188 s

method {:test} Test10() {
var r0 := IsPalindrome("\0\0aaaaaa\0aa\0aaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0\0aaaaaa\0aa\0aaaa\0a"| ==> "\0\0aaaaaa\0aa\0aaaa\0a"[i] == "\0\0aaaaaa\0aa\0aaaa\0a"[|"\0\0aaaaaa\0aa\0aaaa\0a"| - i - 1];
}
method {:test} Test11() {
var r0 := IsPalindrome("\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa"| ==> "\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa"[i] == "\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa"[|"\U{0008}\U{0004}\U{0002}aaaaaa\U{0006}a\naa\U{000C}\0aa"| - i - 1];
}

// REPEAT 6 - TIME: 10.7079609 s

method {:test} Test12() {
var r0 := IsPalindrome("\0aaaaa\0aaa\0\0a\0\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaa\0aaa\0\0a\0\0a"| ==> "\0aaaaa\0aaa\0\0a\0\0a"[i] == "\0aaaaa\0aaa\0\0a\0\0a"[|"\0aaaaa\0aaa\0\0a\0\0a"| - i - 1];
}
method {:test} Test13() {
var r0 := IsPalindrome("\U{0002}\U{0004}aaaaaaaa\U{0006}\U{0008}aa\naa\U{000C}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\U{0004}aaaaaaaa\U{0006}\U{0008}aa\naa\U{000C}\0"| ==> "\U{0002}\U{0004}aaaaaaaa\U{0006}\U{0008}aa\naa\U{000C}\0"[i] == "\U{0002}\U{0004}aaaaaaaa\U{0006}\U{0008}aa\naa\U{000C}\0"[|"\U{0002}\U{0004}aaaaaaaa\U{0006}\U{0008}aa\naa\U{000C}\0"| - i - 1];
}

// REPEAT 7 - TIME: 11.8101326 s

method {:test} Test14() {
var r0 := IsPalindrome("\0\0aaaaaa\0aa\0aa\0a\0aaa");
expect r0 <==> forall i :: 0 <= i < |"\0\0aaaaaa\0aa\0aa\0a\0aaa"| ==> "\0\0aaaaaa\0aa\0aa\0a\0aaa"[i] == "\0\0aaaaaa\0aa\0aa\0a\0aaa"[|"\0\0aaaaaa\0aa\0aa\0a\0aaa"| - i - 1];
}
method {:test} Test15() {
var r0 := IsPalindrome("\U{0006}\0\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0\U{0002}\U{0004}"| ==> "\U{0006}\0\U{0002}\U{0004}"[i] == "\U{0006}\0\U{0002}\U{0004}"[|"\U{0006}\0\U{0002}\U{0004}"| - i - 1];
}

// REPEAT 8 - TIME: 12.986437 s

method {:test} Test16() {
var r0 := IsPalindrome("\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] == "\0a"[|"\0a"| - i - 1];
}
method {:test} Test17() {
var r0 := IsPalindrome("a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a");
expect r0 <==> forall i :: 0 <= i < |"a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a"| ==> "a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a"[i] == "a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a"[|"a\U{0002}a\U{0006}aaa\U{0004}aaa\U{0008}aa\na\U{000C}\0\U{000E}\U{0010}a"| - i - 1];
}

// REPEAT 9 - TIME: 14.3127529 s

method {:test} Test18() {
var r0 := IsPalindrome("a\0a\0aaaaaaa\0aaaaa\0\0\0\0\0\0");
expect r0 <==> forall i :: 0 <= i < |"a\0a\0aaaaaaa\0aaaaa\0\0\0\0\0\0"| ==> "a\0a\0aaaaaaa\0aaaaa\0\0\0\0\0\0"[i] == "a\0a\0aaaaaaa\0aaaaa\0\0\0\0\0\0"[|"a\0a\0aaaaaaa\0aaaaa\0\0\0\0\0\0"| - i - 1];
}
method {:test} Test19() {
var r0 := IsPalindrome("\U{0004}\0a\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0a\U{0002}"| ==> "\U{0004}\0a\U{0002}"[i] == "\U{0004}\0a\U{0002}"[|"\U{0004}\0a\U{0002}"| - i - 1];
}

// REPEAT 10 - TIME: 15.5908245 s

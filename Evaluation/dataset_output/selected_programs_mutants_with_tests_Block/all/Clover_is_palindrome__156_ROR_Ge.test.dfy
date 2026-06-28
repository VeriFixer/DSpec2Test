// Clover_is_palindrome.dfy

method {:testEntry} IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1]
{
  if |x| >= 0 {
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


method {:test} Test0() {
var r0 := IsPalindrome("\0\0");
expect r0 <==> forall i :: 0 <= i < |"\0\0"| ==> "\0\0"[i] == "\0\0"[|"\0\0"| - i - 1];
}
method {:test} Test1() {
var r0 := IsPalindrome("\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0002}"| ==> "\0\U{0002}"[i] == "\0\U{0002}"[|"\0\U{0002}"| - i - 1];
}
method {:test} Test2() {
var r0 := IsPalindrome("");
expect r0 <==> forall i :: 0 <= i < |""| ==> ""[i] == ""[|""| - i - 1];
}

// REPEAT 1 - TIME: 2.9014999 s

method {:test} Test3() {
var r0 := IsPalindrome("\0a\U{0004}aaaaaaaaaa\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\0a\U{0004}aaaaaaaaaa\U{0002}\0"| ==> "\0a\U{0004}aaaaaaaaaa\U{0002}\0"[i] == "\0a\U{0004}aaaaaaaaaa\U{0002}\0"[|"\0a\U{0004}aaaaaaaaaa\U{0002}\0"| - i - 1];
}
method {:test} Test4() {
var r0 := IsPalindrome("\0aaa\U{0004}aaaaaaaaaaaaaaaaa\U{0006}a\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aaa\U{0004}aaaaaaaaaaaaaaaaa\U{0006}a\U{0002}"| ==> "\0aaa\U{0004}aaaaaaaaaaaaaaaaa\U{0006}a\U{0002}"[i] == "\0aaa\U{0004}aaaaaaaaaaaaaaaaa\U{0006}a\U{0002}"[|"\0aaa\U{0004}aaaaaaaaaaaaaaaaa\U{0006}a\U{0002}"| - i - 1];
}
method {:test} Test5() {
var r0 := IsPalindrome("\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}\0"| ==> "\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}\0"[i] == "\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}\0"[|"\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0002}\0"| - i - 1];
}

// REPEAT 2 - TIME: 4.4508555 s

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

method {:test} Test12() {
var r0 := IsPalindrome("\0\naaaaa\U{0002}a\U{0004}a\U{0006}aaa\U{0008}a\U{000C}\0");
expect r0 <==> forall i :: 0 <= i < |"\0\naaaaa\U{0002}a\U{0004}a\U{0006}aaa\U{0008}a\U{000C}\0"| ==> "\0\naaaaa\U{0002}a\U{0004}a\U{0006}aaa\U{0008}a\U{000C}\0"[i] == "\0\naaaaa\U{0002}a\U{0004}a\U{0006}aaa\U{0008}a\U{000C}\0"[|"\0\naaaaa\U{0002}a\U{0004}a\U{0006}aaa\U{0008}a\U{000C}\0"| - i - 1];
}
method {:test} Test13() {
var r0 := IsPalindrome("\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}"| ==> "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}"[i] == "\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}"[|"\U{0002}\0aaaaaaaaaaaaaaaaa\U{0004}"| - i - 1];
}
method {:test} Test14() {
var r0 := IsPalindrome("\0\U{000E}aa\U{0004}aa\U{0006}aaaaaaa\U{0008}\n\U{000C}\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\0\U{000E}aa\U{0004}aa\U{0006}aaaaaaa\U{0008}\n\U{000C}\U{0002}\0"| ==> "\0\U{000E}aa\U{0004}aa\U{0006}aaaaaaa\U{0008}\n\U{000C}\U{0002}\0"[i] == "\0\U{000E}aa\U{0004}aa\U{0006}aaaaaaa\U{0008}\n\U{000C}\U{0002}\0"[|"\0\U{000E}aa\U{0004}aa\U{0006}aaaaaaa\U{0008}\n\U{000C}\U{0002}\0"| - i - 1];
}

// REPEAT 5 - TIME: 9.2023411 s

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

method {:test} Test21() {
var r0 := IsPalindrome("\0aa\U{0002}aaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}a\na\U{0006}\U{000E}\0");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}a\na\U{0006}\U{000E}\0"| ==> "\0aa\U{0002}aaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}a\na\U{0006}\U{000E}\0"[i] == "\0aa\U{0002}aaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}a\na\U{0006}\U{000E}\0"[|"\0aa\U{0002}aaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}a\na\U{0006}\U{000E}\0"| - i - 1];
}
method {:test} Test22() {
var r0 := IsPalindrome("\0\U{0004}aaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0004}aaaaa\U{0002}"| ==> "\0\U{0004}aaaaa\U{0002}"[i] == "\0\U{0004}aaaaa\U{0002}"[|"\0\U{0004}aaaaa\U{0002}"| - i - 1];
}
method {:test} Test23() {
var r0 := IsPalindrome("\0aa\U{0002}aaaaaaaaaaaaaaaa\U{0006}aa\U{0004}a\0");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaaaa\U{0006}aa\U{0004}a\0"| ==> "\0aa\U{0002}aaaaaaaaaaaaaaaa\U{0006}aa\U{0004}a\0"[i] == "\0aa\U{0002}aaaaaaaaaaaaaaaa\U{0006}aa\U{0004}a\0"[|"\0aa\U{0002}aaaaaaaaaaaaaaaa\U{0006}aa\U{0004}a\0"| - i - 1];
}

// REPEAT 8 - TIME: 14.0561754 s

method {:test} Test24() {
var r0 := IsPalindrome("\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0"| ==> "\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0"[i] == "\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0"[|"\0aa\U{0004}aaaaaaaaaaa\U{0002}aaa\U{0006}aaaaaa\U{0008}a\0"| - i - 1];
}
method {:test} Test25() {
var r0 := IsPalindrome("\0\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0004}\U{0002}"| ==> "\0\U{0004}\U{0002}"[i] == "\0\U{0004}\U{0002}"[|"\0\U{0004}\U{0002}"| - i - 1];
}
method {:test} Test26() {
var r0 := IsPalindrome("\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0"| ==> "\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0"[i] == "\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0"[|"\0aaaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0008}\U{0006}a\0"| - i - 1];
}

// REPEAT 9 - TIME: 15.4333324 s

method {:test} Test27() {
var r0 := IsPalindrome("\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0006}\0");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0006}\0"| ==> "\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0006}\0"[i] == "\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0006}\0"[|"\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0006}\0"| - i - 1];
}
method {:test} Test28() {
var r0 := IsPalindrome("\0\U{0004}\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0004}\U{0002}"| ==> "\0\U{0004}\U{0002}"[i] == "\0\U{0004}\U{0002}"[|"\0\U{0004}\U{0002}"| - i - 1];
}
method {:test} Test29() {
var r0 := IsPalindrome("\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0008}\U{0006}\0");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0008}\U{0006}\0"| ==> "\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0008}\U{0006}\0"[i] == "\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0008}\U{0006}\0"[|"\0aa\U{0002}aaaaaaaaaaaaaaa\U{0004}\U{0008}\U{0006}\0"| - i - 1];
}

// REPEAT 10 - TIME: 16.9795037 s

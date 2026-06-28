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


method {:test} Test0() {
var r0 := IsPalindrome("");
expect r0 <==> forall i :: 0 <= i < |""| ==> ""[i] == ""[|""| - i - 1];
}
method {:test} Test2() {
var r0 := IsPalindrome("a");
expect r0 <==> forall i :: 0 <= i < |"a"| ==> "a"[i] == "a"[|"a"| - i - 1];
}
method {:test} Test3() {
var r0 := IsPalindrome("aa");
expect r0 <==> forall i :: 0 <= i < |"aa"| ==> "aa"[i] == "aa"[|"aa"| - i - 1];
}
method {:test} Test8() {
var r0 := IsPalindrome("aa\U{0002}aaaaa\0aa");
expect r0 <==> forall i :: 0 <= i < |"aa\U{0002}aaaaa\0aa"| ==> "aa\U{0002}aaaaa\0aa"[i] == "aa\U{0002}aaaaa\0aa"[|"aa\U{0002}aaaaa\0aa"| - i - 1];
}
method {:test} Test9() {
var r0 := IsPalindrome("\0\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0002}"| ==> "\0\U{0002}"[i] == "\0\U{0002}"[|"\0\U{0002}"| - i - 1];
}
method {:test} Test10() {
var r0 := IsPalindrome("aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa");
expect r0 <==> forall i :: 0 <= i < |"aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa"| ==> "aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa"[i] == "aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa"[|"aaaaaa\0aaaaaaaaaaaaaa\U{0002}aaaaaa"| - i - 1];
}
method {:test} Test12() {
var r0 := IsPalindrome("\U{0002}aaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaaaa\0"| ==> "\U{0002}aaaaaaa\0"[i] == "\U{0002}aaaaaaa\0"[|"\U{0002}aaaaaaa\0"| - i - 1];
}
method {:test} Test13() {
var r0 := IsPalindrome("aa\U{0002}aaa\0aa");
expect r0 <==> forall i :: 0 <= i < |"aa\U{0002}aaa\0aa"| ==> "aa\U{0002}aaa\0aa"[i] == "aa\U{0002}aaa\0aa"[|"aa\U{0002}aaa\0aa"| - i - 1];
}

// REPEAT 1 - TIME: 14.1660893 s

method {:test} Test14() {
var r0 := IsPalindrome("\0a\0\U{0002}a\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\0\U{0002}a\0a"| ==> "\0a\0\U{0002}a\0a"[i] == "\0a\0\U{0002}a\0a"[|"\0a\0\U{0002}a\0a"| - i - 1];
}
method {:test} Test15() {
var r0 := IsPalindrome("\U{0006}\0aaaaaa\U{0002}\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\0aaaaaa\U{0002}\U{0004}"| ==> "\U{0006}\0aaaaaa\U{0002}\U{0004}"[i] == "\U{0006}\0aaaaaa\U{0002}\U{0004}"[|"\U{0006}\0aaaaaa\U{0002}\U{0004}"| - i - 1];
}

// REPEAT 2 - TIME: 16.1204056 s

method {:test} Test16() {
var r0 := IsPalindrome("\0aa\U{0002}aaaaaa\0\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aa\U{0002}aaaaaa\0\0a"| ==> "\0aa\U{0002}aaaaaa\0\0a"[i] == "\0aa\U{0002}aaaaaa\0\0a"[|"\0aa\U{0002}aaaaaa\0\0a"| - i - 1];
}
method {:test} Test17() {
var r0 := IsPalindrome("\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a"| ==> "\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a"[i] == "\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a"[|"\U{0008}\U{0004}\U{0002}aaa\0\U{0006}a"| - i - 1];
}

// REPEAT 3 - TIME: 17.885548 s

method {:test} Test18() {
var r0 := IsPalindrome("\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a"| ==> "\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a"[i] == "\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a"[|"\0a\0aaaaaaaaaaaa\0aaaaa\0aaaaaa\0a"| - i - 1];
}
method {:test} Test19() {
var r0 := IsPalindrome("\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0"| ==> "\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0"[i] == "\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0"[|"\U{0004}\U{0002}aaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa\0"| - i - 1];
}

// REPEAT 4 - TIME: 19.8975657 s

method {:test} Test20() {
var r0 := IsPalindrome("a\0\0");
expect r0 <==> forall i :: 0 <= i < |"a\0\0"| ==> "a\0\0"[i] == "a\0\0"[|"a\0\0"| - i - 1];
}
method {:test} Test21() {
var r0 := IsPalindrome("\U{0004}\U{0002}\0aaaa\U{0006}a\n\U{0008}\U{000C}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}\0aaaa\U{0006}a\n\U{0008}\U{000C}"| ==> "\U{0004}\U{0002}\0aaaa\U{0006}a\n\U{0008}\U{000C}"[i] == "\U{0004}\U{0002}\0aaaa\U{0006}a\n\U{0008}\U{000C}"[|"\U{0004}\U{0002}\0aaaa\U{0006}a\n\U{0008}\U{000C}"| - i - 1];
}

// REPEAT 5 - TIME: 21.6229226 s

method {:test} Test22() {
var r0 := IsPalindrome("\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a");
expect r0 <==> forall i :: 0 <= i < |"\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a"| ==> "\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a"[i] == "\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a"[|"\0\0\0aaaa\0a\0a\0a\0a\0aa\0aaaaaaa\0a\0a"| - i - 1];
}
method {:test} Test23() {
var r0 := IsPalindrome("\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n");
expect r0 <==> forall i :: 0 <= i < |"\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n"| ==> "\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n"[i] == "\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n"[|"\U{000C}aa\0aaa\U{0002}a\U{0004}\U{0006}aaaaaaa\U{0008}\n"| - i - 1];
}

// REPEAT 6 - TIME: 23.5892715 s

method {:test} Test24() {
var r0 := IsPalindrome("a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0"| ==> "a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0"[i] == "a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0"[|"a\0aaaaa\0aaa\0a\0a\0\0aaaaa\0aaaa\0\0"| - i - 1];
}
method {:test} Test25() {
var r0 := IsPalindrome("\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}"| ==> "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}"[i] == "\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}"[|"\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\0aaaaaaa\U{0006}"| - i - 1];
}

// REPEAT 7 - TIME: 25.6409536 s

method {:test} Test26() {
var r0 := IsPalindrome("a\0\0aaaaa\0aaa\0a\0\0aa\0");
expect r0 <==> forall i :: 0 <= i < |"a\0\0aaaaa\0aaa\0a\0\0aa\0"| ==> "a\0\0aaaaa\0aaa\0a\0\0aa\0"[i] == "a\0\0aaaaa\0aaa\0a\0\0aa\0"[|"a\0\0aaaaa\0aaa\0a\0\0aa\0"| - i - 1];
}
method {:test} Test27() {
var r0 := IsPalindrome("\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}");
expect r0 <==> forall i :: 0 <= i < |"\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}"| ==> "\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}"[i] == "\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}"[|"\U{001A}\U{0004}a\U{0006}aaa\n\U{0002}\U{0008}a\U{0014}a\U{0016}aa\U{000C}aaaa\0aaa\U{000E}a\U{0012}\U{0010}\U{0018}"| - i - 1];
}

// REPEAT 8 - TIME: 27.5096495 s

method {:test} Test28() {
var r0 := IsPalindrome("\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a"| ==> "\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a"[i] == "\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a"[|"\0aaaaaaaaaaaa\0a\0\0\0a\U{0002}aaaaa\0a"| - i - 1];
}
method {:test} Test29() {
var r0 := IsPalindrome("\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}");
expect r0 <==> forall i :: 0 <= i < |"\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}"| ==> "\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}"[i] == "\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}"[|"\U{0010}\U{0004}aaaaa\U{0006}\0\U{0008}aa\U{0002}\naaaaa\U{000C}\U{000E}"| - i - 1];
}

// REPEAT 9 - TIME: 29.3311426 s

method {:test} Test30() {
var r0 := IsPalindrome("a\0aaaaaaaaaaaa\0\0a\0a\0\0\0aaaaa\0\0");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaaaaaaa\0\0a\0a\0\0\0aaaaa\0\0"| ==> "a\0aaaaaaaaaaaa\0\0a\0a\0\0\0aaaaa\0\0"[i] == "a\0aaaaaaaaaaaa\0\0a\0a\0\0\0aaaaa\0\0"[|"a\0aaaaaaaaaaaa\0\0a\0a\0\0\0aaaaa\0\0"| - i - 1];
}
method {:test} Test31() {
var r0 := IsPalindrome("\U{0004}\U{0002}aaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}aaaa\0a"| ==> "\U{0004}\U{0002}aaaa\0a"[i] == "\U{0004}\U{0002}aaaa\0a"[|"\U{0004}\U{0002}aaaa\0a"| - i - 1];
}

// REPEAT 10 - TIME: 31.6432081 s

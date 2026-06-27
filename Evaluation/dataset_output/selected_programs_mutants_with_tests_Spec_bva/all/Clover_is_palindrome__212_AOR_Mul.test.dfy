// Clover_is_palindrome.dfy

method {:testEntry} IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1]
{
  if |x| == 0 {
    return true;
  }
  var i := 0;
  var j := |x| * 1;
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

// REPEAT 1 - TIME: 9.0194992 s

method {:test} Test14() {
var r0 := IsPalindrome("\0\0a\0aa");
expect r0 <==> forall i :: 0 <= i < |"\0\0a\0aa"| ==> "\0\0a\0aa"[i] == "\0\0a\0aa"[|"\0\0a\0aa"| - i - 1];
}
method {:test} Test15() {
var r0 := IsPalindrome("\U{0006}\U{0002}aaaaaa\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\U{0002}aaaaaa\0\U{0004}"| ==> "\U{0006}\U{0002}aaaaaa\0\U{0004}"[i] == "\U{0006}\U{0002}aaaaaa\0\U{0004}"[|"\U{0006}\U{0002}aaaaaa\0\U{0004}"| - i - 1];
}

// REPEAT 2 - TIME: 10.0381582 s

method {:test} Test16() {
var r0 := IsPalindrome("aa\0aaaa\0\0\0");
expect r0 <==> forall i :: 0 <= i < |"aa\0aaaa\0\0\0"| ==> "aa\0aaaa\0\0\0"[i] == "aa\0aaaa\0\0\0"[|"aa\0aaaa\0\0\0"| - i - 1];
}
method {:test} Test17() {
var r0 := IsPalindrome("\U{0002}\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0\U{0004}"| ==> "\U{0002}\0\U{0004}"[i] == "\U{0002}\0\U{0004}"[|"\U{0002}\0\U{0004}"| - i - 1];
}

// REPEAT 3 - TIME: 11.0799511 s

method {:test} Test18() {
var r0 := IsPalindrome("\0\0\0aaaaa\0\0aaaaaaaaaaaaaaaa\0\0a");
expect r0 <==> forall i :: 0 <= i < |"\0\0\0aaaaa\0\0aaaaaaaaaaaaaaaa\0\0a"| ==> "\0\0\0aaaaa\0\0aaaaaaaaaaaaaaaa\0\0a"[i] == "\0\0\0aaaaa\0\0aaaaaaaaaaaaaaaa\0\0a"[|"\0\0\0aaaaa\0\0aaaaaaaaaaaaaaaa\0\0a"| - i - 1];
}
method {:test} Test19() {
var r0 := IsPalindrome("\U{0006}\U{0002}\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0006}\U{0002}\0\U{0004}"| ==> "\U{0006}\U{0002}\0\U{0004}"[i] == "\U{0006}\U{0002}\0\U{0004}"[|"\U{0006}\U{0002}\0\U{0004}"| - i - 1];
}

// REPEAT 4 - TIME: 12.0576775 s

method {:test} Test20() {
var r0 := IsPalindrome("\0\0\0a");
expect r0 <==> forall i :: 0 <= i < |"\0\0\0a"| ==> "\0\0\0a"[i] == "\0\0\0a"[|"\0\0\0a"| - i - 1];
}
method {:test} Test21() {
var r0 := IsPalindrome("\U{0008}aa\U{0002}aaa\U{0006}\0\U{0004}\n\U{000C}");
expect r0 <==> forall i :: 0 <= i < |"\U{0008}aa\U{0002}aaa\U{0006}\0\U{0004}\n\U{000C}"| ==> "\U{0008}aa\U{0002}aaa\U{0006}\0\U{0004}\n\U{000C}"[i] == "\U{0008}aa\U{0002}aaa\U{0006}\0\U{0004}\n\U{000C}"[|"\U{0008}aa\U{0002}aaa\U{0006}\0\U{0004}\n\U{000C}"| - i - 1];
}

// REPEAT 5 - TIME: 13.0218693 s

method {:test} Test22() {
var r0 := IsPalindrome("\0aaaaaaaaaa\0\0aaaaaa\0aaaa\0\0a\0\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaaaa\0\0aaaaaa\0aaaa\0\0a\0\0a"| ==> "\0aaaaaaaaaa\0\0aaaaaa\0aaaa\0\0a\0\0a"[i] == "\0aaaaaaaaaa\0\0aaaaaa\0aaaa\0\0a\0\0a"[|"\0aaaaaaaaaa\0\0aaaaaa\0aaaa\0\0a\0\0a"| - i - 1];
}
method {:test} Test23() {
var r0 := IsPalindrome("\naa\U{0002}aaaa\0\U{0006}\U{0004}\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\naa\U{0002}aaaa\0\U{0006}\U{0004}\U{0008}"| ==> "\naa\U{0002}aaaa\0\U{0006}\U{0004}\U{0008}"[i] == "\naa\U{0002}aaaa\0\U{0006}\U{0004}\U{0008}"[|"\naa\U{0002}aaaa\0\U{0006}\U{0004}\U{0008}"| - i - 1];
}

// REPEAT 6 - TIME: 13.9068567 s

method {:test} Test24() {
var r0 := IsPalindrome("a\0aaaaaaa\0a\0aaaaaaa\0a\0aaaaaa\0\0");
expect r0 <==> forall i :: 0 <= i < |"a\0aaaaaaa\0a\0aaaaaaa\0a\0aaaaaa\0\0"| ==> "a\0aaaaaaa\0a\0aaaaaaa\0a\0aaaaaa\0\0"[i] == "a\0aaaaaaa\0a\0aaaaaaa\0a\0aaaaaa\0\0"[|"a\0aaaaaaa\0a\0aaaaaaa\0a\0aaaaaa\0\0"| - i - 1];
}
method {:test} Test25() {
var r0 := IsPalindrome("\U{0002}\0aaaaaaa\U{0004}a\U{000C}a\U{0010}aaa\U{0008}\U{000E}\naa\U{0006}aaaaa\U{0012}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0aaaaaaa\U{0004}a\U{000C}a\U{0010}aaa\U{0008}\U{000E}\naa\U{0006}aaaaa\U{0012}"| ==> "\U{0002}\0aaaaaaa\U{0004}a\U{000C}a\U{0010}aaa\U{0008}\U{000E}\naa\U{0006}aaaaa\U{0012}"[i] == "\U{0002}\0aaaaaaa\U{0004}a\U{000C}a\U{0010}aaa\U{0008}\U{000E}\naa\U{0006}aaaaa\U{0012}"[|"\U{0002}\0aaaaaaa\U{0004}a\U{000C}a\U{0010}aaa\U{0008}\U{000E}\naa\U{0006}aaaaa\U{0012}"| - i - 1];
}

// REPEAT 7 - TIME: 14.824686 s

method {:test} Test26() {
var r0 := IsPalindrome("\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a"| ==> "\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a"[i] == "\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a"[|"\0a\0a\0aaaa\0a\0aaaaaaaaaaaaaa\0a\0a"| - i - 1];
}
method {:test} Test27() {
var r0 := IsPalindrome("\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a"| ==> "\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a"[i] == "\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a"[|"\U{0016}\U{0004}aa\U{0008}aa\U{0002}a\U{000C}a\U{0010}aaa\U{000E}aa\n\U{0012}aa\0\U{0006}aaaa\U{0014}a"| - i - 1];
}

// REPEAT 8 - TIME: 15.7315768 s

method {:test} Test28() {
var r0 := IsPalindrome("\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a"| ==> "\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a"[i] == "\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a"[|"\0aaaaaaaa\0\0a\0\0a\0\0\0aaaaa\0a"| - i - 1];
}
method {:test} Test29() {
var r0 := IsPalindrome("\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a");
expect r0 <==> forall i :: 0 <= i < |"\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a"| ==> "\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a"[i] == "\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a"[|"\U{0014}\U{0002}aaaaaaa\na\U{0012}a\U{000E}\U{000C}\U{0010}aaaaaa\U{0008}\U{0004}aa\U{0006}\0a"| - i - 1];
}

// REPEAT 9 - TIME: 16.6845595 s

method {:test} Test30() {
var r0 := IsPalindrome("\0a\0aaaaaaaaaaaaaaaaaaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\0aaaaaaaaaaaaaaaaaaaaaa\0a"| ==> "\0a\0aaaaaaaaaaaaaaaaaaaaaa\0a"[i] == "\0a\0aaaaaaaaaaaaaaaaaaaaaa\0a"[|"\0a\0aaaaaaaaaaaaaaaaaaaaaa\0a"| - i - 1];
}
method {:test} Test31() {
var r0 := IsPalindrome("\U{0004}\U{0002}aaaa\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}aaaa\0"| ==> "\U{0004}\U{0002}aaaa\0"[i] == "\U{0004}\U{0002}aaaa\0"[|"\U{0004}\U{0002}aaaa\0"| - i - 1];
}

// REPEAT 10 - TIME: 17.6597556 s

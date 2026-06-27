// Clover_is_palindrome.dfy

method {:testEntry} IsPalindrome(x: seq<char>) returns (result: bool)
  ensures result <==> forall i :: 0 <= i < |x| ==> x[i] == x[|x| - i - 1]
{
  if true {
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
method {:test} Test1() {
var r0 := IsPalindrome("aa\U{0002}aaaaa\0aa");
expect r0 <==> forall i :: 0 <= i < |"aa\U{0002}aaaaa\0aa"| ==> "aa\U{0002}aaaaa\0aa"[i] == "aa\U{0002}aaaaa\0aa"[|"aa\U{0002}aaaaa\0aa"| - i - 1];
}

// REPEAT 1 - TIME: 3.2404079 s

method {:test} Test2() {
var r0 := IsPalindrome("\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a"| ==> "\0a"[i] == "\0a"[|"\0a"| - i - 1];
}
method {:test} Test3() {
var r0 := IsPalindrome("aa\U{0002}aaaaaaaaaaa\0a\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"aa\U{0002}aaaaaaaaaaa\0a\U{0004}"| ==> "aa\U{0002}aaaaaaaaaaa\0a\U{0004}"[i] == "aa\U{0002}aaaaaaaaaaa\0a\U{0004}"[|"aa\U{0002}aaaaaaaaaaa\0a\U{0004}"| - i - 1];
}

// REPEAT 2 - TIME: 4.9196574 s

method {:test} Test4() {
var r0 := IsPalindrome("\0aaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0aaaa\0a"| ==> "\0aaaa\0a"[i] == "\0aaaa\0a"[|"\0aaaa\0a"| - i - 1];
}
method {:test} Test5() {
var r0 := IsPalindrome("\0aaaaaaa\U{0002}");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaaa\U{0002}"| ==> "\0aaaaaaa\U{0002}"[i] == "\0aaaaaaa\U{0002}"[|"\0aaaaaaa\U{0002}"| - i - 1];
}

// REPEAT 3 - TIME: 6.29407 s

method {:test} Test6() {
var r0 := IsPalindrome("\0aaaaaa\0a\0aaaaa\0aa");
expect r0 <==> forall i :: 0 <= i < |"\0aaaaaa\0a\0aaaaa\0aa"| ==> "\0aaaaaa\0a\0aaaaa\0aa"[i] == "\0aaaaaa\0a\0aaaaa\0aa"[|"\0aaaaaa\0a\0aaaaa\0aa"| - i - 1];
}
method {:test} Test7() {
var r0 := IsPalindrome("\U{0002}aaaaa\0\U{0004}");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}aaaaa\0\U{0004}"| ==> "\U{0002}aaaaa\0\U{0004}"[i] == "\U{0002}aaaaa\0\U{0004}"[|"\U{0002}aaaaa\0\U{0004}"| - i - 1];
}

// REPEAT 4 - TIME: 7.8796447 s

method {:test} Test8() {
var r0 := IsPalindrome("\0a\0\0");
expect r0 <==> forall i :: 0 <= i < |"\0a\0\0"| ==> "\0a\0\0"[i] == "\0a\0\0"[|"\0a\0\0"| - i - 1];
}
method {:test} Test9() {
var r0 := IsPalindrome("\U{0002}\0");
expect r0 <==> forall i :: 0 <= i < |"\U{0002}\0"| ==> "\U{0002}\0"[i] == "\U{0002}\0"[|"\U{0002}\0"| - i - 1];
}

// REPEAT 5 - TIME: 9.5452844 s

method {:test} Test10() {
var r0 := IsPalindrome("\0\U{0002}\0\0\0a\0");
expect r0 <==> forall i :: 0 <= i < |"\0\U{0002}\0\0\0a\0"| ==> "\0\U{0002}\0\0\0a\0"[i] == "\0\U{0002}\0\0\0a\0"[|"\0\U{0002}\0\0\0a\0"| - i - 1];
}
method {:test} Test11() {
var r0 := IsPalindrome("\U{0004}aaaaa\U{0002}a\0aaaaa\U{0006}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}aaaaa\U{0002}a\0aaaaa\U{0006}"| ==> "\U{0004}aaaaa\U{0002}a\0aaaaa\U{0006}"[i] == "\U{0004}aaaaa\U{0002}a\0aaaaa\U{0006}"[|"\U{0004}aaaaa\U{0002}a\0aaaaa\U{0006}"| - i - 1];
}

// REPEAT 6 - TIME: 11.0310593 s

method {:test} Test12() {
var r0 := IsPalindrome("\0a\0\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\0\0a"| ==> "\0a\0\0a"[i] == "\0a\0\0a"[|"\0a\0\0a"| - i - 1];
}
method {:test} Test13() {
var r0 := IsPalindrome("\U{0004}\U{0008}\U{0002}\0\U{0006}a");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0008}\U{0002}\0\U{0006}a"| ==> "\U{0004}\U{0008}\U{0002}\0\U{0006}a"[i] == "\U{0004}\U{0008}\U{0002}\0\U{0006}a"[|"\U{0004}\U{0008}\U{0002}\0\U{0006}a"| - i - 1];
}

// REPEAT 7 - TIME: 12.1953848 s

method {:test} Test14() {
var r0 := IsPalindrome("\0a\U{0002}aaaaaaa\0a");
expect r0 <==> forall i :: 0 <= i < |"\0a\U{0002}aaaaaaa\0a"| ==> "\0a\U{0002}aaaaaaa\0a"[i] == "\0a\U{0002}aaaaaaa\0a"[|"\0a\U{0002}aaaaaaa\0a"| - i - 1];
}
method {:test} Test15() {
var r0 := IsPalindrome("\U{0004}\0a\U{0006}\U{0002}\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\0a\U{0006}\U{0002}\U{0008}"| ==> "\U{0004}\0a\U{0006}\U{0002}\U{0008}"[i] == "\U{0004}\0a\U{0006}\U{0002}\U{0008}"[|"\U{0004}\0a\U{0006}\U{0002}\U{0008}"| - i - 1];
}

// REPEAT 8 - TIME: 13.3435537 s

method {:test} Test16() {
var r0 := IsPalindrome("\0a\0\0\0\0");
expect r0 <==> forall i :: 0 <= i < |"\0a\0\0\0\0"| ==> "\0a\0\0\0\0"[i] == "\0a\0\0\0\0"[|"\0a\0\0\0\0"| - i - 1];
}
method {:test} Test17() {
var r0 := IsPalindrome("\U{0004}\U{0002}a\U{0006}\0\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\U{0004}\U{0002}a\U{0006}\0\U{0008}"| ==> "\U{0004}\U{0002}a\U{0006}\0\U{0008}"[i] == "\U{0004}\U{0002}a\U{0006}\0\U{0008}"[|"\U{0004}\U{0002}a\U{0006}\0\U{0008}"| - i - 1];
}

// REPEAT 9 - TIME: 14.6283499 s

method {:test} Test18() {
var r0 := IsPalindrome("\0\0\0");
expect r0 <==> forall i :: 0 <= i < |"\0\0\0"| ==> "\0\0\0"[i] == "\0\0\0"[|"\0\0\0"| - i - 1];
}
method {:test} Test19() {
var r0 := IsPalindrome("\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}");
expect r0 <==> forall i :: 0 <= i < |"\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}"| ==> "\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}"[i] == "\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}"[|"\n\U{0002}aaaaa\U{0004}a\U{0006}\0\U{0008}"| - i - 1];
}

// REPEAT 10 - TIME: 15.8060666 s

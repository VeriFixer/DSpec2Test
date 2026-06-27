// Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings1.dfy

predicate isPrefixPredicate(pre: string, str: string)
{
  |str| >= |pre| &&
  pre <= str
}

method {:testEntry} isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| >= |str| {
    return false;
  }
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
    decreases |pre| - i
  {
    if pre[i] != str[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

predicate isSubstringPredicate(sub: string, str: string)
{
  |str| >= |sub| &&
  exists i :: 
    0 <= i <= |str| &&
    isPrefixPredicate(sub, str[i..])
}

method {:testEntry} isSubstring(sub: string, str: string) returns (res: bool)
  ensures res == isSubstringPredicate(sub, str)
{
  if |sub| > |str| {
    return false;
  }
  var i := |str| - |sub|;
  while i >= 0
    invariant i >= -1
    invariant forall j :: i < j <= |str| - |sub| ==> !isPrefixPredicate(sub, str[j..])
    decreases i
  {
    var isPref := isPrefix(sub, str[i..]);
    if isPref {
      return true;
    }
    i := i - 1;
  }
  return false;
}

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k &&
  |str2| >= k &&
  exists i :: 
    0 <= i <= |str1| - k &&
    isSubstringPredicate(str1[i..][..k], str2)
}

method {:testEntry} haveCommonKSubstring(k: nat, str1: string, str2: string)
    returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k, str1, str2) == found
{
  if |str1| < k || |str2| < k {
    return false;
  }
  var i := |str1| - k;
  while i >= 0
    invariant i >= -1
    invariant forall j :: i < j <= |str1| - k ==> !isSubstringPredicate(str1[j..][..k], str2)
    decreases i
  {
    var isSub := isSubstring(str1[i..][..k], str2);
    if isSub {
      return true;
    }
    i := i - 1;
  }
  return false;
}

predicate maxCommonSubstringPredicate(str1: string, str2: string, len: nat)
{
  forall k :: 
    len < k <= |str1| ==>
      !haveCommonKSubstringPredicate(k, str1, str2)
}

method {:testEntry} maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  ensures len <= |str1| && len <= |str2|
  ensures len >= 0
  ensures maxCommonSubstringPredicate(str1, str2, len)
{
  var i := |str1|;
  while i > 0
    invariant i >= 0
    invariant forall j :: i < j <= |str1| ==> !haveCommonKSubstringPredicate(j, str1, str2)
    decreases i
  {
    var ans := haveCommonKSubstring(i, str1, str2);
    if ans {
      return i;
    }
    i := i - 1;
  }
  assert i == 0;
  return 0;
}


method {:test} Test0() {
var r0 := isPrefix("a", "a");
expect |"a"| > |"a"| ==> !r0;
expect r0 == isPrefixPredicate("a", "a");
}
method {:test} Test1() {
var r0 := isPrefix("aaaaaaaa\0", "aaaaaaaa\U{0002}");
expect |"aaaaaaaa\0"| > |"aaaaaaaa\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaa\0", "aaaaaaaa\U{0002}");
}
method {:test} Test2() {
var r0 := isPrefix("aaaaaaa", "aaaaaa");
expect |"aaaaaaa"| > |"aaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaa", "aaaaaa");
}
method {:test} Test3() {
var r0 := isSubstring("a", "aaaaaaaaaaa");
expect r0 == isSubstringPredicate("a", "aaaaaaaaaaa");
}
method {:test} Test4() {
var r0 := isSubstring("aa", "a");
expect r0 == isSubstringPredicate("aa", "a");
}
method {:test} Test5() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaa", "aaaaaaa");
expect |"aaaaaaaaaaa"| < 1 || |"aaaaaaa"| < 1 ==> !r0;
expect haveCommonKSubstringPredicate(1, "aaaaaaaaaaa", "aaaaaaa") == r0;
}
method {:test} Test6() {
var r0 := haveCommonKSubstring(0, "a", "a");
expect |"a"| < 0 || |"a"| < 0 ==> !r0;
expect haveCommonKSubstringPredicate(0, "a", "a") == r0;
}
method {:test} Test7() {
var r0 := haveCommonKSubstring(10, "aaaaaaaaa", "");
expect |"aaaaaaaaa"| < 10 || |""| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "aaaaaaaaa", "") == r0;
}
method {:test} Test8() {
var r0 := maxCommonSubstringLength("a", "a");
expect r0 <= |"a"| && r0 <= |"a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a", "a", r0);
}

// REPEAT 1 - TIME: 8.8295699 s

method {:test} Test9() {
var r0 := isPrefix("\U{0002}\0", "\U{0002}\0");
expect |"\U{0002}\0"| > |"\U{0002}\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0", "\U{0002}\0");
}
method {:test} Test10() {
var r0 := isPrefix("a\U{0002}aaaaa\U{0008}a\n", "aaaaaa\U{0006}\U{0004}a\0");
expect |"a\U{0002}aaaaa\U{0008}a\n"| > |"aaaaaa\U{0006}\U{0004}a\0"| ==> !r0;
expect r0 == isPrefixPredicate("a\U{0002}aaaaa\U{0008}a\n", "aaaaaa\U{0006}\U{0004}a\0");
}
method {:test} Test11() {
var r0 := isPrefix("\U{0008}\0aaaaa\U{0006}", "\naa\U{0002}aa\U{0004}");
expect |"\U{0008}\0aaaaa\U{0006}"| > |"\naa\U{0002}aa\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}\0aaaaa\U{0006}", "\naa\U{0002}aa\U{0004}");
}
method {:test} Test12() {
var r0 := isSubstring("a\0\U{0004}aaaaaaaaa", "aaaaaaaaa\U{0002}a\U{0006}a\0\U{0004}aaaaaaaaa");
expect r0 == isSubstringPredicate("a\0\U{0004}aaaaaaaaa", "aaaaaaaaa\U{0002}a\U{0006}a\0\U{0004}aaaaaaaaa");
}
method {:test} Test13() {
var r0 := isSubstring("aa\U{0002}", "a\0");
expect r0 == isSubstringPredicate("aa\U{0002}", "a\0");
}
method {:test} Test14() {
var r0 := haveCommonKSubstring(11, "\U{0002}aaaaaaaaaaaaaaaa", "\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaa"| < 11 || |"\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "\U{0002}aaaaaaaaaaaaaaaa", "\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test15() {
var r0 := haveCommonKSubstring(11, "\U{0004}\0aaaaaaaaa", "\U{0002}aaaaaaaaaa");
expect |"\U{0004}\0aaaaaaaaa"| < 11 || |"\U{0002}aaaaaaaaaa"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "\U{0004}\0aaaaaaaaa", "\U{0002}aaaaaaaaaa") == r0;
}
method {:test} Test16() {
var r0 := haveCommonKSubstring(11, "\U{0004}a", "a\0aaaaa\U{0002}");
expect |"\U{0004}a"| < 11 || |"a\0aaaaa\U{0002}"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "\U{0004}a", "a\0aaaaa\U{0002}") == r0;
}
method {:test} Test17() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "a\0");
expect r0 <= |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 <= |"a\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "a\0", r0);
}

// REPEAT 2 - TIME: 14.1308062 s

method {:test} Test18() {
var r0 := isPrefix("\U{0008}\U{0002}\U{0004}", "\U{0008}\U{0002}\U{0004}\U{0006}a\0aaa");
expect |"\U{0008}\U{0002}\U{0004}"| > |"\U{0008}\U{0002}\U{0004}\U{0006}a\0aaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}\U{0002}\U{0004}", "\U{0008}\U{0002}\U{0004}\U{0006}a\0aaa");
}
method {:test} Test19() {
var r0 := isPrefix("\U{0002}aaa", "\U{0004}\0aa");
expect |"\U{0002}aaa"| > |"\U{0004}\0aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}aaa", "\U{0004}\0aa");
}
method {:test} Test20() {
var r0 := isPrefix("\U{0004}\0aaaaa\U{0006}aaaaaaaa", "\U{0008}a\U{0002}");
expect |"\U{0004}\0aaaaa\U{0006}aaaaaaaa"| > |"\U{0008}a\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0aaaaa\U{0006}aaaaaaaa", "\U{0008}a\U{0002}");
}
method {:test} Test21() {
var r0 := isSubstring("\U{0004}\0aa\U{0006}aaa", "\U{0002}\U{0004}\0aa\U{0006}aaa");
expect r0 == isSubstringPredicate("\U{0004}\0aa\U{0006}aaa", "\U{0002}\U{0004}\0aa\U{0006}aaa");
}
method {:test} Test22() {
var r0 := isSubstring("\U{0004}\0aa", "\U{0006}a\U{0002}");
expect r0 == isSubstringPredicate("\U{0004}\0aa", "\U{0006}a\U{0002}");
}
method {:test} Test23() {
var r0 := haveCommonKSubstring(12, "\U{0002}aaaaaaaaaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaa"| < 12 || |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "\U{0002}aaaaaaaaaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test24() {
var r0 := haveCommonKSubstring(12, "\U{0004}aaaaaaaaa\U{0002}a", "\U{0006}\0aaaaaaaaaa");
expect |"\U{0004}aaaaaaaaa\U{0002}a"| < 12 || |"\U{0006}\0aaaaaaaaaa"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "\U{0004}aaaaaaaaa\U{0002}a", "\U{0006}\0aaaaaaaaaa") == r0;
}
method {:test} Test25() {
var r0 := haveCommonKSubstring(12, "\U{0004}a\U{0002}", "\n\0aaaaa\U{0006}\U{0008}");
expect |"\U{0004}a\U{0002}"| < 12 || |"\n\0aaaaa\U{0006}\U{0008}"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "\U{0004}a\U{0002}", "\n\0aaaaa\U{0006}\U{0008}") == r0;
}
method {:test} Test26() {
var r0 := maxCommonSubstringLength("\U{0006}\U{0002}", "\U{0004}\0");
expect r0 <= |"\U{0006}\U{0002}"| && r0 <= |"\U{0004}\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}\U{0002}", "\U{0004}\0", r0);
}

// REPEAT 3 - TIME: 18.7962525 s

method {:test} Test27() {
var r0 := isPrefix("\U{0004}\0aaaaa\na\U{000E}a\U{0002}\U{0006}aaa\U{0010}", "\U{0004}\0aaaaa\na\U{000E}a\U{0002}\U{0006}aaa\U{0010}aaaaa\U{0008}aaa\U{000C}");
expect |"\U{0004}\0aaaaa\na\U{000E}a\U{0002}\U{0006}aaa\U{0010}"| > |"\U{0004}\0aaaaa\na\U{000E}a\U{0002}\U{0006}aaa\U{0010}aaaaa\U{0008}aaa\U{000C}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0aaaaa\na\U{000E}a\U{0002}\U{0006}aaa\U{0010}", "\U{0004}\0aaaaa\na\U{000E}a\U{0002}\U{0006}aaa\U{0010}aaaaa\U{0008}aaa\U{000C}");
}
method {:test} Test28() {
var r0 := isPrefix("\U{0004}\0", "\U{0002}a");
expect |"\U{0004}\0"| > |"\U{0002}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0", "\U{0002}a");
}
method {:test} Test29() {
var r0 := isPrefix("\U{0010}aaaa\U{0002}a\U{000C}a\U{0006}a", "\U{0004}\0aaa\U{0008}a\na\U{000E}");
expect |"\U{0010}aaaa\U{0002}a\U{000C}a\U{0006}a"| > |"\U{0004}\0aaa\U{0008}a\na\U{000E}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0010}aaaa\U{0002}a\U{000C}a\U{0006}a", "\U{0004}\0aaa\U{0008}a\na\U{000E}");
}
method {:test} Test30() {
var r0 := isSubstring("\n\U{0006}\U{0002}", "\U{0008}aaaaaa\U{0004}aaa\0\n\U{0006}\U{0002}");
expect r0 == isSubstringPredicate("\n\U{0006}\U{0002}", "\U{0008}aaaaaa\U{0004}aaa\0\n\U{0006}\U{0002}");
}
method {:test} Test31() {
var r0 := isSubstring("\U{0008}\0aa\U{0004}a\U{0006}", "\na\U{0002}");
expect r0 == isSubstringPredicate("\U{0008}\0aa\U{0004}a\U{0006}", "\na\U{0002}");
}
method {:test} Test32() {
var r0 := haveCommonKSubstring(13, "\U{0002}\0aaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}\0aaaaaaaaaaaaaaa"| < 13 || |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "\U{0002}\0aaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test33() {
var r0 := haveCommonKSubstring(13, "\U{0002}\0aaaaaaaaaa\U{0006}", "\U{000C}aaaaaaaa\U{0004}a\U{0008}\n");
expect |"\U{0002}\0aaaaaaaaaa\U{0006}"| < 13 || |"\U{000C}aaaaaaaa\U{0004}a\U{0008}\n"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "\U{0002}\0aaaaaaaaaa\U{0006}", "\U{000C}aaaaaaaa\U{0004}a\U{0008}\n") == r0;
}
method {:test} Test34() {
var r0 := haveCommonKSubstring(15, "\U{0006}\U{0002}aaaaaaaaaaaa", "\U{0008}aaaaa\0\U{0004}");
expect |"\U{0006}\U{0002}aaaaaaaaaaaa"| < 15 || |"\U{0008}aaaaa\0\U{0004}"| < 15 ==> !r0;
expect haveCommonKSubstringPredicate(15, "\U{0006}\U{0002}aaaaaaaaaaaa", "\U{0008}aaaaa\0\U{0004}") == r0;
}
method {:test} Test35() {
var r0 := maxCommonSubstringLength("\U{0006}aa", "\U{0004}\0aaaaaaaaaaaaaa\U{0002}");
expect r0 <= |"\U{0006}aa"| && r0 <= |"\U{0004}\0aaaaaaaaaaaaaa\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}aa", "\U{0004}\0aaaaaaaaaaaaaa\U{0002}", r0);
}

// REPEAT 4 - TIME: 24.1031283 s

method {:test} Test36() {
var r0 := isPrefix("\U{0004}\0\U{0002}a\U{0006}", "\U{0004}\0\U{0002}a\U{0006}\U{0008}");
expect |"\U{0004}\0\U{0002}a\U{0006}"| > |"\U{0004}\0\U{0002}a\U{0006}\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0\U{0002}a\U{0006}", "\U{0004}\0\U{0002}a\U{0006}\U{0008}");
}
method {:test} Test37() {
var r0 := isPrefix("\naa\U{0006}\U{0002}", "\U{000C}\0\U{0004}a\U{0008}");
expect |"\naa\U{0006}\U{0002}"| > |"\U{000C}\0\U{0004}a\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\naa\U{0006}\U{0002}", "\U{000C}\0\U{0004}a\U{0008}");
}
method {:test} Test38() {
var r0 := isPrefix("\U{0010}aaa\U{0002}a\U{0008}aa", "\U{000E}\0aa\U{0006}\U{0004}\n\U{000C}");
expect |"\U{0010}aaa\U{0002}a\U{0008}aa"| > |"\U{000E}\0aa\U{0006}\U{0004}\n\U{000C}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0010}aaa\U{0002}a\U{0008}aa", "\U{000E}\0aa\U{0006}\U{0004}\n\U{000C}");
}
method {:test} Test39() {
var r0 := isSubstring("\n\0a\U{0004}\U{0006}", "aaa\U{0002}aaaaa\U{0008}\n\0a\U{0004}\U{0006}a");
expect r0 == isSubstringPredicate("\n\0a\U{0004}\U{0006}", "aaa\U{0002}aaaaa\U{0008}\n\0a\U{0004}\U{0006}a");
}
method {:test} Test40() {
var r0 := isSubstring("\U{0004}aaaaaa\U{0006}", "\U{0002}\0");
expect r0 == isSubstringPredicate("\U{0004}aaaaaa\U{0006}", "\U{0002}\0");
}
method {:test} Test41() {
var r0 := haveCommonKSubstring(16, "\U{0006}aa\U{0002}aaaaaaaaaa\U{0008}aaaaaaaaa", "\U{0004}\0aaaaaaaa\U{0008}aaaaaaaaa");
expect |"\U{0006}aa\U{0002}aaaaaaaaaa\U{0008}aaaaaaaaa"| < 16 || |"\U{0004}\0aaaaaaaa\U{0008}aaaaaaaaa"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "\U{0006}aa\U{0002}aaaaaaaaaa\U{0008}aaaaaaaaa", "\U{0004}\0aaaaaaaa\U{0008}aaaaaaaaa") == r0;
}
method {:test} Test42() {
var r0 := haveCommonKSubstring(16, "\naaaaa\U{0002}aaaaa\U{0004}aaa", "\U{0008}\0aaaaa\U{0006}aaaaaaaa");
expect |"\naaaaa\U{0002}aaaaa\U{0004}aaa"| < 16 || |"\U{0008}\0aaaaa\U{0006}aaaaaaaa"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "\naaaaa\U{0002}aaaaa\U{0004}aaa", "\U{0008}\0aaaaa\U{0006}aaaaaaaa") == r0;
}
method {:test} Test43() {
var r0 := haveCommonKSubstring(19, "\U{0004}a\U{0002}aaaaaaaa\U{000C}\n\U{0012}\U{0014}aa\U{0016}", "a\0aaaaa\U{0006}a\U{0008}a\U{000E}aaaaaaaaaaaaaaa\U{0010}aa");
expect |"\U{0004}a\U{0002}aaaaaaaa\U{000C}\n\U{0012}\U{0014}aa\U{0016}"| < 19 || |"a\0aaaaa\U{0006}a\U{0008}a\U{000E}aaaaaaaaaaaaaaa\U{0010}aa"| < 19 ==> !r0;
expect haveCommonKSubstringPredicate(19, "\U{0004}a\U{0002}aaaaaaaa\U{000C}\n\U{0012}\U{0014}aa\U{0016}", "a\0aaaaa\U{0006}a\U{0008}a\U{000E}aaaaaaaaaaaaaaa\U{0010}aa") == r0;
}
method {:test} Test44() {
var r0 := maxCommonSubstringLength("\U{0006}a\U{0004}a", "\U{0002}\0");
expect r0 <= |"\U{0006}a\U{0004}a"| && r0 <= |"\U{0002}\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}a\U{0004}a", "\U{0002}\0", r0);
}

// REPEAT 5 - TIME: 28.8112645 s

method {:test} Test45() {
var r0 := isPrefix("\0aa\U{0004}\U{0002}\U{0006}", "\0aa\U{0004}\U{0002}\U{0006}\n\U{0008}");
expect |"\0aa\U{0004}\U{0002}\U{0006}"| > |"\0aa\U{0004}\U{0002}\U{0006}\n\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\0aa\U{0004}\U{0002}\U{0006}", "\0aa\U{0004}\U{0002}\U{0006}\n\U{0008}");
}
method {:test} Test46() {
var r0 := isPrefix("aaa\U{0002}aa\U{0008}a\U{0006}\U{0012}\U{0016}a\U{000C}", "\n\0\U{0004}aaaa\U{000E}a\U{0014}\U{0010}\U{0018}a");
expect |"aaa\U{0002}aa\U{0008}a\U{0006}\U{0012}\U{0016}a\U{000C}"| > |"\n\0\U{0004}aaaa\U{000E}a\U{0014}\U{0010}\U{0018}a"| ==> !r0;
expect r0 == isPrefixPredicate("aaa\U{0002}aa\U{0008}a\U{0006}\U{0012}\U{0016}a\U{000C}", "\n\0\U{0004}aaaa\U{000E}a\U{0014}\U{0010}\U{0018}a");
}
method {:test} Test47() {
var r0 := isPrefix("aaaa\U{0004}\U{000C}a\U{0006}a\U{0014}a\U{0012}a\n\U{0016}aa\U{0018}", "a\0aaaaa\U{000E}\U{0008}\U{0002}\U{0010}");
expect |"aaaa\U{0004}\U{000C}a\U{0006}a\U{0014}a\U{0012}a\n\U{0016}aa\U{0018}"| > |"a\0aaaaa\U{000E}\U{0008}\U{0002}\U{0010}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaa\U{0004}\U{000C}a\U{0006}a\U{0014}a\U{0012}a\n\U{0016}aa\U{0018}", "a\0aaaaa\U{000E}\U{0008}\U{0002}\U{0010}");
}
method {:test} Test48() {
var r0 := isSubstring("\n\0aa\U{0008}\U{000C}", "\U{0006}aaaaaaaaaa\U{0004}aaaa\U{0002}\n\0aa\U{0008}\U{000C}");
expect r0 == isSubstringPredicate("\n\0aa\U{0008}\U{000C}", "\U{0006}aaaaaaaaaa\U{0004}aaaa\U{0002}\n\0aa\U{0008}\U{000C}");
}
method {:test} Test49() {
var r0 := isSubstring("\U{0004}\0aaaa\n\U{000C}aa\U{0002}\U{0008}\U{0012}", "\U{0006}aaaaaaaa\U{000E}a\U{0010}");
expect r0 == isSubstringPredicate("\U{0004}\0aaaa\n\U{000C}aa\U{0002}\U{0008}\U{0012}", "\U{0006}aaaaaaaa\U{000E}a\U{0010}");
}
method {:test} Test50() {
var r0 := haveCommonKSubstring(20, "aa\U{0002}aaaaaa\U{0004}aaaaaaaaa\U{000C}aa\U{0014}a\U{0010}\U{0012}aa\U{000E}\U{0016}", "\U{0018}\0aaaaa\U{0006}\U{0008}\naaaaaaaaa\U{000C}aa\U{0014}a\U{0010}\U{0012}aa\U{000E}\U{0016}");
expect |"aa\U{0002}aaaaaa\U{0004}aaaaaaaaa\U{000C}aa\U{0014}a\U{0010}\U{0012}aa\U{000E}\U{0016}"| < 20 || |"\U{0018}\0aaaaa\U{0006}\U{0008}\naaaaaaaaa\U{000C}aa\U{0014}a\U{0010}\U{0012}aa\U{000E}\U{0016}"| < 20 ==> !r0;
expect haveCommonKSubstringPredicate(20, "aa\U{0002}aaaaaa\U{0004}aaaaaaaaa\U{000C}aa\U{0014}a\U{0010}\U{0012}aa\U{000E}\U{0016}", "\U{0018}\0aaaaa\U{0006}\U{0008}\naaaaaaaaa\U{000C}aa\U{0014}a\U{0010}\U{0012}aa\U{000E}\U{0016}") == r0;
}
method {:test} Test51() {
var r0 := haveCommonKSubstring(20, "\U{0006}aaaaaaaaaaaaaaaa\U{0002}aa", "\U{0004}\0aaaaaaaaaaaaaaaaaaa");
expect |"\U{0006}aaaaaaaaaaaaaaaa\U{0002}aa"| < 20 || |"\U{0004}\0aaaaaaaaaaaaaaaaaaa"| < 20 ==> !r0;
expect haveCommonKSubstringPredicate(20, "\U{0006}aaaaaaaaaaaaaaaa\U{0002}aa", "\U{0004}\0aaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test52() {
var r0 := haveCommonKSubstring(58, "\U{0008}aa\U{0002}", "\U{0006}\0aaaaa\U{0004}aa");
expect |"\U{0008}aa\U{0002}"| < 58 || |"\U{0006}\0aaaaa\U{0004}aa"| < 58 ==> !r0;
expect haveCommonKSubstringPredicate(58, "\U{0008}aa\U{0002}", "\U{0006}\0aaaaa\U{0004}aa") == r0;
}
method {:test} Test53() {
var r0 := maxCommonSubstringLength("a\0a\U{0004}a", "\U{0002}aa");
expect r0 <= |"a\0a\U{0004}a"| && r0 <= |"\U{0002}aa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0a\U{0004}a", "\U{0002}aa", r0);
}

// REPEAT 6 - TIME: 34.7663096 s

method {:test} Test54() {
var r0 := isPrefix("\U{0006}aaa\U{0002}\U{0004}\0", "\U{0006}aaa\U{0002}\U{0004}\0\U{0008}aaaa");
expect |"\U{0006}aaa\U{0002}\U{0004}\0"| > |"\U{0006}aaa\U{0002}\U{0004}\0\U{0008}aaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}aaa\U{0002}\U{0004}\0", "\U{0006}aaa\U{0002}\U{0004}\0\U{0008}aaaa");
}
method {:test} Test55() {
var r0 := isPrefix("\0", "\U{0004}a\U{0002}aa");
expect |"\0"| > |"\U{0004}a\U{0002}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\0", "\U{0004}a\U{0002}aa");
}
method {:test} Test56() {
var r0 := isPrefix("aaaaa\U{000E}aaa a&\U{000C}a\"aa*aa\U{0002}\U{001C}\U{0004}a\U{0008}aa\U{0014},", "a\0aaaaa\U{0016}a\U{001A}\U{0018}\n\U{0010}($aaa\U{0012}\U{001E}aaaa\U{0006}aa.");
expect |"aaaaa\U{000E}aaa a&\U{000C}a\"aa*aa\U{0002}\U{001C}\U{0004}a\U{0008}aa\U{0014},"| > |"a\0aaaaa\U{0016}a\U{001A}\U{0018}\n\U{0010}($aaa\U{0012}\U{001E}aaaa\U{0006}aa."| ==> !r0;
expect r0 == isPrefixPredicate("aaaaa\U{000E}aaa a&\U{000C}a\"aa*aa\U{0002}\U{001C}\U{0004}a\U{0008}aa\U{0014},", "a\0aaaaa\U{0016}a\U{001A}\U{0018}\n\U{0010}($aaa\U{0012}\U{001E}aaaa\U{0006}aa.");
}
method {:test} Test57() {
var r0 := isSubstring("\n\0\U{000C}\U{0006}a", "\U{0004}a\U{0002}\U{0008}\n\0\U{000C}\U{0006}a");
expect r0 == isSubstringPredicate("\n\0\U{000C}\U{0006}a", "\U{0004}a\U{0002}\U{0008}\n\0\U{000C}\U{0006}a");
}
method {:test} Test58() {
var r0 := isSubstring("\U{0004}aa\U{0008}\U{000C}\U{000E}", "\U{0002}\0\U{0006}\n");
expect r0 == isSubstringPredicate("\U{0004}aa\U{0008}\U{000C}\U{000E}", "\U{0002}\0\U{0006}\n");
}
method {:test} Test59() {
var r0 := haveCommonKSubstring(21, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"| < 21 || |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 21 ==> !r0;
expect haveCommonKSubstringPredicate(21, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test60() {
var r0 := haveCommonKSubstring(21, "aaaaaaaaaaaaaaa\U{000C}a\U{000E}\0aaaa\U{0010}\U{0012}", "\U{0016}aaaaaa\U{0002}a\U{0006}\U{0004}\naaa\U{0008}aaaaaaaaaaa\U{0014}a");
expect |"aaaaaaaaaaaaaaa\U{000C}a\U{000E}\0aaaa\U{0010}\U{0012}"| < 21 || |"\U{0016}aaaaaa\U{0002}a\U{0006}\U{0004}\naaa\U{0008}aaaaaaaaaaa\U{0014}a"| < 21 ==> !r0;
expect haveCommonKSubstringPredicate(21, "aaaaaaaaaaaaaaa\U{000C}a\U{000E}\0aaaa\U{0010}\U{0012}", "\U{0016}aaaaaa\U{0002}a\U{0006}\U{0004}\naaa\U{0008}aaaaaaaaaaa\U{0014}a") == r0;
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(59, "\U{0008}aaaaaa\0aa\U{0002}a", "\U{0006}aaaaaa\U{0004}a");
expect |"\U{0008}aaaaaa\0aa\U{0002}a"| < 59 || |"\U{0006}aaaaaa\U{0004}a"| < 59 ==> !r0;
expect haveCommonKSubstringPredicate(59, "\U{0008}aaaaaa\0aa\U{0002}a", "\U{0006}aaaaaa\U{0004}a") == r0;
}
method {:test} Test62() {
var r0 := maxCommonSubstringLength("\U{0004}\0", "\U{0006}a\U{0002}");
expect r0 <= |"\U{0004}\0"| && r0 <= |"\U{0006}a\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}\0", "\U{0006}a\U{0002}", r0);
}

// REPEAT 7 - TIME: 41.1209983 s

method {:test} Test63() {
var r0 := isPrefix("\U{001E}\0aaa\U{0008}aa\U{0004}\U{0014}\n\U{0016}\U{0006}\U{000E}aaa\U{000C}\U{0002}\U{001A}", "\U{001E}\0aaa\U{0008}aa\U{0004}\U{0014}\n\U{0016}\U{0006}\U{000E}aaa\U{000C}\U{0002}\U{001A}\U{0018}\U{0012}aaaaa\U{0010}\U{001C}a");
expect |"\U{001E}\0aaa\U{0008}aa\U{0004}\U{0014}\n\U{0016}\U{0006}\U{000E}aaa\U{000C}\U{0002}\U{001A}"| > |"\U{001E}\0aaa\U{0008}aa\U{0004}\U{0014}\n\U{0016}\U{0006}\U{000E}aaa\U{000C}\U{0002}\U{001A}\U{0018}\U{0012}aaaaa\U{0010}\U{001C}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{001E}\0aaa\U{0008}aa\U{0004}\U{0014}\n\U{0016}\U{0006}\U{000E}aaa\U{000C}\U{0002}\U{001A}", "\U{001E}\0aaa\U{0008}aa\U{0004}\U{0014}\n\U{0016}\U{0006}\U{000E}aaa\U{000C}\U{0002}\U{001A}\U{0018}\U{0012}aaaaa\U{0010}\U{001C}a");
}
method {:test} Test64() {
var r0 := isPrefix(" aaaaaa\U{000E}\U{0002}aa\U{001A}\U{000C}\U{0016}\U{0006}aaa\0", "\U{001E}aaaaaa\U{0004}a\U{0012}aaa\U{0014}\n\U{0010}\U{0008}\U{001C}\U{0018}");
expect |" aaaaaa\U{000E}\U{0002}aa\U{001A}\U{000C}\U{0016}\U{0006}aaa\0"| > |"\U{001E}aaaaaa\U{0004}a\U{0012}aaa\U{0014}\n\U{0010}\U{0008}\U{001C}\U{0018}"| ==> !r0;
expect r0 == isPrefixPredicate(" aaaaaa\U{000E}\U{0002}aa\U{001A}\U{000C}\U{0016}\U{0006}aaa\0", "\U{001E}aaaaaa\U{0004}a\U{0012}aaa\U{0014}\n\U{0010}\U{0008}\U{001C}\U{0018}");
}
method {:test} Test65() {
var r0 := isPrefix("aaaaaaaaaaa\U{0006}aa\U{0012}aa\U{001A}a\U{0008}aaaa\U{0002}aaa\U{0014}\U{0018}", "aaaaa\U{0004}a\0a\U{000C}\U{000E}\U{0010}\n\U{0016}");
expect |"aaaaaaaaaaa\U{0006}aa\U{0012}aa\U{001A}a\U{0008}aaaa\U{0002}aaa\U{0014}\U{0018}"| > |"aaaaa\U{0004}a\0a\U{000C}\U{000E}\U{0010}\n\U{0016}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaaaa\U{0006}aa\U{0012}aa\U{001A}a\U{0008}aaaa\U{0002}aaa\U{0014}\U{0018}", "aaaaa\U{0004}a\0a\U{000C}\U{000E}\U{0010}\n\U{0016}");
}
method {:test} Test66() {
var r0 := isSubstring("\U{0014}aaaaaa\U{0012}\U{0010}a\U{0002}\U{000E}\U{0004}\U{001A}a\n", "\0aaaaa\U{000C}a\U{0008}\U{0016}\U{0006}\U{0018}\U{001C}\U{0014}aaaaaa\U{0012}\U{0010}a\U{0002}\U{000E}\U{0004}\U{001A}a\n\U{001E}");
expect r0 == isSubstringPredicate("\U{0014}aaaaaa\U{0012}\U{0010}a\U{0002}\U{000E}\U{0004}\U{001A}a\n", "\0aaaaa\U{000C}a\U{0008}\U{0016}\U{0006}\U{0018}\U{001C}\U{0014}aaaaaa\U{0012}\U{0010}a\U{0002}\U{000E}\U{0004}\U{001A}a\n\U{001E}");
}
method {:test} Test67() {
var r0 := isSubstring("\U{000C}\0aaa\U{0008}a\na\U{0004}a", "\U{000E}aa\U{0002}a\U{0006}aaaa");
expect r0 == isSubstringPredicate("\U{000C}\0aaa\U{0008}a\na\U{0004}a", "\U{000E}aa\U{0002}a\U{0006}aaaa");
}
method {:test} Test68() {
var r0 := haveCommonKSubstring(22, "\U{0012}aa\U{0004}\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaa\U{0010}\U{000C}", "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\n\U{000E}");
expect |"\U{0012}aa\U{0004}\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaa\U{0010}\U{000C}"| < 22 || |"\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\n\U{000E}"| < 22 ==> !r0;
expect haveCommonKSubstringPredicate(22, "\U{0012}aa\U{0004}\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaa\U{0010}\U{000C}", "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaa\n\U{000E}") == r0;
}
method {:test} Test69() {
var r0 := haveCommonKSubstring(26, "\U{0018}aaaaaaa\0aaaaa\U{0008}\U{0002}aaa\U{000C}aaa\U{0010}\U{0014}\U{0016}", "\U{001A}aaaaaaaa\U{0004}aaa\U{000E}a\naaaaaaaaa\U{0012}a\U{0006}aa");
expect |"\U{0018}aaaaaaa\0aaaaa\U{0008}\U{0002}aaa\U{000C}aaa\U{0010}\U{0014}\U{0016}"| < 26 || |"\U{001A}aaaaaaaa\U{0004}aaa\U{000E}a\naaaaaaaaa\U{0012}a\U{0006}aa"| < 26 ==> !r0;
expect haveCommonKSubstringPredicate(26, "\U{0018}aaaaaaa\0aaaaa\U{0008}\U{0002}aaa\U{000C}aaa\U{0010}\U{0014}\U{0016}", "\U{001A}aaaaaaaa\U{0004}aaa\U{000E}a\naaaaaaaaa\U{0012}a\U{0006}aa") == r0;
}
method {:test} Test70() {
var r0 := haveCommonKSubstring(60, "\U{000E}aaa\U{0002}aaa\0aaaaa\n", "\U{0010}aaaaaaaa\U{0004}a\U{0006}a\U{0008}aa\U{000C}");
expect |"\U{000E}aaa\U{0002}aaa\0aaaaa\n"| < 60 || |"\U{0010}aaaaaaaa\U{0004}a\U{0006}a\U{0008}aa\U{000C}"| < 60 ==> !r0;
expect haveCommonKSubstringPredicate(60, "\U{000E}aaa\U{0002}aaa\0aaaaa\n", "\U{0010}aaaaaaaa\U{0004}a\U{0006}a\U{0008}aa\U{000C}") == r0;
}
method {:test} Test71() {
var r0 := maxCommonSubstringLength("\U{0008}\U{0004}", "\0\U{0002}aaaaaa\U{0006}aaaaaaaa\n");
expect r0 <= |"\U{0008}\U{0004}"| && r0 <= |"\0\U{0002}aaaaaa\U{0006}aaaaaaaa\n"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0008}\U{0004}", "\0\U{0002}aaaaaa\U{0006}aaaaaaaa\n", r0);
}

// REPEAT 8 - TIME: 47.7171716 s

method {:test} Test72() {
var r0 := isPrefix("\U{0012}aaaaaa\U{0002}a\U{0006}\n\U{000E}", "\U{0012}aaaaaa\U{0002}a\U{0006}\n\U{000E}a\U{0010}\U{0008}\U{000C}a\U{0004}\0a");
expect |"\U{0012}aaaaaa\U{0002}a\U{0006}\n\U{000E}"| > |"\U{0012}aaaaaa\U{0002}a\U{0006}\n\U{000E}a\U{0010}\U{0008}\U{000C}a\U{0004}\0a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0012}aaaaaa\U{0002}a\U{0006}\n\U{000E}", "\U{0012}aaaaaa\U{0002}a\U{0006}\n\U{000E}a\U{0010}\U{0008}\U{000C}a\U{0004}\0a");
}
method {:test} Test73() {
var r0 := isPrefix("(aa\U{0006}aa\U{0002}aa\U{001C}\U{0016}\"aaaaa\U{000E}\U{0004}\n\U{0018}a$aaa\U{0008}aa", "a\0aaaaa\U{0010}aa\U{001A}a\U{000C}\U{001E}aaaaaaaa\U{0014}aa \U{0012}a&");
expect |"(aa\U{0006}aa\U{0002}aa\U{001C}\U{0016}\"aaaaa\U{000E}\U{0004}\n\U{0018}a$aaa\U{0008}aa"| > |"a\0aaaaa\U{0010}aa\U{001A}a\U{000C}\U{001E}aaaaaaaa\U{0014}aa \U{0012}a&"| ==> !r0;
expect r0 == isPrefixPredicate("(aa\U{0006}aa\U{0002}aa\U{001C}\U{0016}\"aaaaa\U{000E}\U{0004}\n\U{0018}a$aaa\U{0008}aa", "a\0aaaaa\U{0010}aa\U{001A}a\U{000C}\U{001E}aaaaaaaa\U{0014}aa \U{0012}a&");
}
method {:test} Test74() {
var r0 := isPrefix("aaaaa\U{0008}aaa\U{0004}aaa\U{000C}aaa\U{0018}\U{0012}\0\U{001A}aaaa\U{001C}", "\U{001E}aa\U{0002}a\na\U{0006}\U{000E}aa\U{0010}a\U{0014}\U{0016}");
expect |"aaaaa\U{0008}aaa\U{0004}aaa\U{000C}aaa\U{0018}\U{0012}\0\U{001A}aaaa\U{001C}"| > |"\U{001E}aa\U{0002}a\na\U{0006}\U{000E}aa\U{0010}a\U{0014}\U{0016}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaa\U{0008}aaa\U{0004}aaa\U{000C}aaa\U{0018}\U{0012}\0\U{001A}aaaa\U{001C}", "\U{001E}aa\U{0002}a\na\U{0006}\U{000E}aa\U{0010}a\U{0014}\U{0016}");
}
method {:test} Test75() {
var r0 := isSubstring("\U{001E}aa\0\U{0006}\naa\U{000E}aa\U{0018}\U{0010}\U{001A}", "\U{0004}aaaaa\U{0008}aa\U{0012}\U{000C}\U{0002}\U{0016}\U{0014}a\U{001E}aa\0\U{0006}\naa\U{000E}aa\U{0018}\U{0010}\U{001A}\U{001C}");
expect r0 == isSubstringPredicate("\U{001E}aa\0\U{0006}\naa\U{000E}aa\U{0018}\U{0010}\U{001A}", "\U{0004}aaaaa\U{0008}aa\U{0012}\U{000C}\U{0002}\U{0016}\U{0014}a\U{001E}aa\0\U{0006}\naa\U{000E}aa\U{0018}\U{0010}\U{001A}\U{001C}");
}
method {:test} Test76() {
var r0 := isSubstring("a\0aaa\U{0014}\U{0016}\U{001A}aaa\U{0018}\"&\U{000C}\U{0006}aa,aaaa\U{0010}a\n", "\U{0004}\U{0002}aaaaaaa\U{000E}\U{001C} aaa(a*$\U{0012}a\U{001E}a.\U{0008}");
expect r0 == isSubstringPredicate("a\0aaa\U{0014}\U{0016}\U{001A}aaa\U{0018}\"&\U{000C}\U{0006}aa,aaaa\U{0010}a\n", "\U{0004}\U{0002}aaaaaaa\U{000E}\U{001C} aaa(a*$\U{0012}a\U{001E}a.\U{0008}");
}
method {:test} Test77() {
var r0 := haveCommonKSubstring(27, "\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}a");
expect |"\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}"| < 27 || |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}a"| < 27 ==> !r0;
expect haveCommonKSubstringPredicate(27, "\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}a") == r0;
}
method {:test} Test78() {
var r0 := haveCommonKSubstring(27, "\U{001A}aaaaaaaaaaaaa\U{0008}a\U{000C}\U{000E}aaa\U{0010}a\na\U{0016}\U{0006}", "\U{0018}aaaaaaaa\0aaa\U{0004}aaaaaaa\U{0014}aaa\U{0012}a\U{0002}");
expect |"\U{001A}aaaaaaaaaaaaa\U{0008}a\U{000C}\U{000E}aaa\U{0010}a\na\U{0016}\U{0006}"| < 27 || |"\U{0018}aaaaaaaa\0aaa\U{0004}aaaaaaa\U{0014}aaa\U{0012}a\U{0002}"| < 27 ==> !r0;
expect haveCommonKSubstringPredicate(27, "\U{001A}aaaaaaaaaaaaa\U{0008}a\U{000C}\U{000E}aaa\U{0010}a\na\U{0016}\U{0006}", "\U{0018}aaaaaaaa\0aaa\U{0004}aaaaaaa\U{0014}aaa\U{0012}a\U{0002}") == r0;
}
method {:test} Test79() {
var r0 := haveCommonKSubstring(61, "\U{001A}aaaaaaaaaaaaaa\U{0004}\n\U{000E}a\U{0010}a\U{0012}a\U{0008}a\U{0016}\U{0006}", "\U{0018}aaaaaaaaaaaa\U{0002}aaa\U{000C}aaa\U{0014}aaaaa\0");
expect |"\U{001A}aaaaaaaaaaaaaa\U{0004}\n\U{000E}a\U{0010}a\U{0012}a\U{0008}a\U{0016}\U{0006}"| < 61 || |"\U{0018}aaaaaaaaaaaa\U{0002}aaa\U{000C}aaa\U{0014}aaaaa\0"| < 61 ==> !r0;
expect haveCommonKSubstringPredicate(61, "\U{001A}aaaaaaaaaaaaaa\U{0004}\n\U{000E}a\U{0010}a\U{0012}a\U{0008}a\U{0016}\U{0006}", "\U{0018}aaaaaaaaaaaa\U{0002}aaa\U{000C}aaa\U{0014}aaaaa\0") == r0;
}
method {:test} Test80() {
var r0 := maxCommonSubstringLength("a\0aaaa", "\U{0002}aa\U{0004}");
expect r0 <= |"a\0aaaa"| && r0 <= |"\U{0002}aa\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0aaaa", "\U{0002}aa\U{0004}", r0);
}

// REPEAT 9 - TIME: 54.6494427 s

method {:test} Test81() {
var r0 := isPrefix("\U{0002}\0a", "\U{0002}\0aa");
expect |"\U{0002}\0a"| > |"\U{0002}\0aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0a", "\U{0002}\0aa");
}
method {:test} Test82() {
var r0 := isPrefix("a\U{0002}aaaaaaaaaaaaaa\U{0014}\U{000C}\U{0008}a\U{0016}aaa\U{0004}", "aaaaaaa\na\U{000E}\U{0010}a\U{0012}aaaa\0aaaaa\U{0018}\U{0006}a");
expect |"a\U{0002}aaaaaaaaaaaaaa\U{0014}\U{000C}\U{0008}a\U{0016}aaa\U{0004}"| > |"aaaaaaa\na\U{000E}\U{0010}a\U{0012}aaaa\0aaaaa\U{0018}\U{0006}a"| ==> !r0;
expect r0 == isPrefixPredicate("a\U{0002}aaaaaaaaaaaaaa\U{0014}\U{000C}\U{0008}a\U{0016}aaa\U{0004}", "aaaaaaa\na\U{000E}\U{0010}a\U{0012}aaaa\0aaaaa\U{0018}\U{0006}a");
}
method {:test} Test83() {
var r0 := isPrefix("\U{0016}aaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{000C}\U{0012}a\U{0014}a\U{0008}", "\U{0018}aaaa\0aaaaa\U{0006}a\naa\U{0004}aa\U{000E}aaaaaaa\U{0010}a");
expect |"\U{0016}aaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{000C}\U{0012}a\U{0014}a\U{0008}"| > |"\U{0018}aaaa\0aaaaa\U{0006}a\naa\U{0004}aa\U{000E}aaaaaaa\U{0010}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0016}aaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{000C}\U{0012}a\U{0014}a\U{0008}", "\U{0018}aaaa\0aaaaa\U{0006}a\naa\U{0004}aa\U{000E}aaaaaaa\U{0010}a");
}
method {:test} Test84() {
var r0 := isSubstring("\U{0006}aaa\U{0002}aa\n\U{000C}", "\U{0014}aaaa\U{0008}aa\U{0004}\U{0010}a\U{000E}a\0a\U{0012}\U{0006}aaa\U{0002}aa\n\U{000C}a");
expect r0 == isSubstringPredicate("\U{0006}aaa\U{0002}aa\n\U{000C}", "\U{0014}aaaa\U{0008}aa\U{0004}\U{0010}a\U{000E}a\0a\U{0012}\U{0006}aaa\U{0002}aa\n\U{000C}a");
}
method {:test} Test85() {
var r0 := isSubstring("\U{0016}aaaaaa\U{0008}a\na\U{0010}a\U{0006}\U{0012}", "\U{0014}aa\U{0002}aaaa\0\U{000C}\U{0004}a\U{000E}");
expect r0 == isSubstringPredicate("\U{0016}aaaaaa\U{0008}a\na\U{0010}a\U{0006}\U{0012}", "\U{0014}aa\U{0002}aaaa\0\U{000C}\U{0004}a\U{000E}");
}
method {:test} Test86() {
var r0 := haveCommonKSubstring(28, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| < 28 || |"\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0004}\0\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}") == r0;
}
method {:test} Test87() {
var r0 := haveCommonKSubstring(28, "aaaaaaaaaaaaaaaaa\U{0008}aaa\U{0004}\naaaaa", "\U{000E}aaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0006}a\0a\U{000C}aa");
expect |"aaaaaaaaaaaaaaaaa\U{0008}aaa\U{0004}\naaaaa"| < 28 || |"\U{000E}aaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0006}a\0a\U{000C}aa"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "aaaaaaaaaaaaaaaaa\U{0008}aaa\U{0004}\naaaaa", "\U{000E}aaaaaaaaaaaa\U{0002}aaaaaaaaa\U{0006}a\0a\U{000C}aa") == r0;
}
method {:test} Test88() {
var r0 := haveCommonKSubstring(62, "\U{000E}aaaaaaaa\0aaaaaaa\U{0008}\n", "\U{0010}aaaaaaaaaaaa\U{0004}a\U{0002}aaaaa\U{000C}a\U{0006}aa");
expect |"\U{000E}aaaaaaaa\0aaaaaaa\U{0008}\n"| < 62 || |"\U{0010}aaaaaaaaaaaa\U{0004}a\U{0002}aaaaa\U{000C}a\U{0006}aa"| < 62 ==> !r0;
expect haveCommonKSubstringPredicate(62, "\U{000E}aaaaaaaa\0aaaaaaa\U{0008}\n", "\U{0010}aaaaaaaaaaaa\U{0004}a\U{0002}aaaaa\U{000C}a\U{0006}aa") == r0;
}
method {:test} Test89() {
var r0 := maxCommonSubstringLength("\0\U{0006}\U{000C}", "\U{0002}\U{0004}a\n\U{0008}");
expect r0 <= |"\0\U{0006}\U{000C}"| && r0 <= |"\U{0002}\U{0004}a\n\U{0008}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\0\U{0006}\U{000C}", "\U{0002}\U{0004}a\n\U{0008}", r0);
}

// REPEAT 10 - TIME: 61.5913655 s

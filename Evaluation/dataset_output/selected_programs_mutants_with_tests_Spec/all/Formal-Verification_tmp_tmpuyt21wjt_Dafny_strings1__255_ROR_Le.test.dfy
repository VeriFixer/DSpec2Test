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
  if |pre| <= |str| {
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

// REPEAT 1 - TIME: 8.0626224 s

method {:test} Test9() {
var r0 := isPrefix("\U{0002}\0a", "\U{0002}\0a");
expect |"\U{0002}\0a"| > |"\U{0002}\0a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0a", "\U{0002}\0a");
}
method {:test} Test10() {
var r0 := isPrefix("\n\U{0002}aaaaa\U{0008}", "\U{0006}aaa\U{0004}aa\0");
expect |"\n\U{0002}aaaaa\U{0008}"| > |"\U{0006}aaa\U{0004}aa\0"| ==> !r0;
expect r0 == isPrefixPredicate("\n\U{0002}aaaaa\U{0008}", "\U{0006}aaa\U{0004}aa\0");
}
method {:test} Test11() {
var r0 := isPrefix("\U{0006}\0aaaaaa", "\U{0008}aa\U{0002}aa\U{0004}");
expect |"\U{0006}\0aaaaaa"| > |"\U{0008}aa\U{0002}aa\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\0aaaaaa", "\U{0008}aa\U{0002}aa\U{0004}");
}
method {:test} Test12() {
var r0 := isSubstring("aaaaaaaaaa\U{0004}aaaaaaaaaaaa\0", "\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaaa\0");
expect r0 == isSubstringPredicate("aaaaaaaaaa\U{0004}aaaaaaaaaaaa\0", "\U{0006}aa\U{0002}aaaaaaaaaaa\U{0004}aaaaaaaaaaaa\0");
}
method {:test} Test13() {
var r0 := isSubstring("a\0aaaaa\U{0002}aaaaa", "aaaaaaaaaaa\U{0004}");
expect r0 == isSubstringPredicate("a\0aaaaa\U{0002}aaaaa", "aaaaaaaaaaa\U{0004}");
}
method {:test} Test14() {
var r0 := haveCommonKSubstring(11, "\U{0008}aa\U{0002}aaaaa\U{0006}aaaaaaaaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaa");
expect |"\U{0008}aa\U{0002}aaaaa\U{0006}aaaaaaaaaaa"| < 11 || |"\U{0004}\0aaaaaaaaaaaaaaaaaa"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "\U{0008}aa\U{0002}aaaaa\U{0006}aaaaaaaaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test15() {
var r0 := haveCommonKSubstring(11, "\U{0006}\0aaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaa");
expect |"\U{0006}\0aaaaaaaaa"| < 11 || |"\U{0004}\U{0002}aaaaaaaaa"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "\U{0006}\0aaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaa") == r0;
}
method {:test} Test16() {
var r0 := haveCommonKSubstring(11, "\U{0006}\U{0002}", "a\0aaaaa\U{0004}");
expect |"\U{0006}\U{0002}"| < 11 || |"a\0aaaaa\U{0004}"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "\U{0006}\U{0002}", "a\0aaaaa\U{0004}") == r0;
}
method {:test} Test17() {
var r0 := maxCommonSubstringLength("a\0", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <= |"a\0"| && r0 <= |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", r0);
}

// REPEAT 2 - TIME: 11.749385 s

method {:test} Test18() {
var r0 := isPrefix("\U{0004}\0a\U{0002}", "\U{0004}\0a\U{0002}\U{0006}");
expect |"\U{0004}\0a\U{0002}"| > |"\U{0004}\0a\U{0002}\U{0006}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0a\U{0002}", "\U{0004}\0a\U{0002}\U{0006}");
}
method {:test} Test19() {
var r0 := isPrefix("\U{0004}aaaa", "\U{0002}\0aaa");
expect |"\U{0004}aaaa"| > |"\U{0002}\0aaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}aaaa", "\U{0002}\0aaa");
}
method {:test} Test20() {
var r0 := isPrefix("\U{0006}aaaaaa\U{0004}aaa", "\U{0002}\0");
expect |"\U{0006}aaaaaa\U{0004}aaa"| > |"\U{0002}\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}aaaaaa\U{0004}aaa", "\U{0002}\0");
}
method {:test} Test21() {
var r0 := isSubstring("\U{0008}aaaa\0aa\U{0004}aaaaaa", "\U{0006}aaaaaa\U{0002}aaa\U{0008}aaaa\0aa\U{0004}aaaaaa");
expect r0 == isSubstringPredicate("\U{0008}aaaa\0aa\U{0004}aaaaaa", "\U{0006}aaaaaa\U{0002}aaa\U{0008}aaaa\0aa\U{0004}aaaaaa");
}
method {:test} Test22() {
var r0 := isSubstring("\U{0002}\0aaaaaaaaaaa\U{0004}", "\U{0006}aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0002}\0aaaaaaaaaaa\U{0004}", "\U{0006}aaaaaaaaaaaa");
}
method {:test} Test23() {
var r0 := haveCommonKSubstring(13, "\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaa"| < 13 || |"\U{0002}aaaaaaaaaaaaaaaaa"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test24() {
var r0 := haveCommonKSubstring(12, "\U{0008}aaaa\U{0002}aaaa\U{0004}a", "a\0aaaaaaaaaaaaaaaa\U{0006}aa");
expect |"\U{0008}aaaa\U{0002}aaaa\U{0004}a"| < 12 || |"a\0aaaaaaaaaaaaaaaa\U{0006}aa"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "\U{0008}aaaa\U{0002}aaaa\U{0004}a", "a\0aaaaaaaaaaaaaaaa\U{0006}aa") == r0;
}
method {:test} Test25() {
var r0 := haveCommonKSubstring(12, "\n\U{0002}aaaaaaa\U{0004}a\U{0008}", "\U{000C}aaa\0aaaa\U{0006}");
expect |"\n\U{0002}aaaaaaa\U{0004}a\U{0008}"| < 12 || |"\U{000C}aaa\0aaaa\U{0006}"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "\n\U{0002}aaaaaaa\U{0004}a\U{0008}", "\U{000C}aaa\0aaaa\U{0006}") == r0;
}
method {:test} Test26() {
var r0 := maxCommonSubstringLength("a\U{0002}a", "\U{0004}\0");
expect r0 <= |"a\U{0002}a"| && r0 <= |"\U{0004}\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\U{0002}a", "\U{0004}\0", r0);
}

// REPEAT 3 - TIME: 15.4526281 s

method {:test} Test27() {
var r0 := isPrefix("\U{0014}\U{0002}aa\U{0008}\U{000E}aa\n", "\U{0014}\U{0002}aa\U{0008}\U{000E}aa\n\U{0006}a\U{0012}\U{0004}aaaaaaa\U{0010}\U{000C}aaaa\0");
expect |"\U{0014}\U{0002}aa\U{0008}\U{000E}aa\n"| > |"\U{0014}\U{0002}aa\U{0008}\U{000E}aa\n\U{0006}a\U{0012}\U{0004}aaaaaaa\U{0010}\U{000C}aaaa\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0014}\U{0002}aa\U{0008}\U{000E}aa\n", "\U{0014}\U{0002}aa\U{0008}\U{000E}aa\n\U{0006}a\U{0012}\U{0004}aaaaaaa\U{0010}\U{000C}aaaa\0");
}
method {:test} Test28() {
var r0 := isPrefix("\U{0006}\U{0002}", "\U{0004}\0");
expect |"\U{0006}\U{0002}"| > |"\U{0004}\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\U{0002}", "\U{0004}\0");
}
method {:test} Test29() {
var r0 := isPrefix("\U{000E}aaaaa\U{0008}aaa\U{0004}a", "\U{000C}\0\U{0002}aa\U{0006}\n");
expect |"\U{000E}aaaaa\U{0008}aaa\U{0004}a"| > |"\U{000C}\0\U{0002}aa\U{0006}\n"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000E}aaaaa\U{0008}aaa\U{0004}a", "\U{000C}\0\U{0002}aa\U{0006}\n");
}
method {:test} Test30() {
var r0 := isSubstring("\U{0004}aaaa", "\U{0002}aa\0\U{0004}aaaa");
expect r0 == isSubstringPredicate("\U{0004}aaaa", "\U{0002}aa\0\U{0004}aaaa");
}
method {:test} Test31() {
var r0 := isSubstring("\U{0008}\0aaaaa\U{0004}aaaaa", "\U{0006}\U{0002}");
expect r0 == isSubstringPredicate("\U{0008}\0aaaaa\U{0004}aaaaa", "\U{0006}\U{0002}");
}
method {:test} Test32() {
var r0 := haveCommonKSubstring(15, "aaa\U{0002}aaaaaaaa\U{0008}aaaaaaaaaaaaaaaa\U{000E}", "\n\0aaaaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaa\U{000C}");
expect |"aaa\U{0002}aaaaaaaa\U{0008}aaaaaaaaaaaaaaaa\U{000E}"| < 15 || |"\n\0aaaaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaa\U{000C}"| < 15 ==> !r0;
expect haveCommonKSubstringPredicate(15, "aaa\U{0002}aaaaaaaa\U{0008}aaaaaaaaaaaaaaaa\U{000E}", "\n\0aaaaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaa\U{000C}") == r0;
}
method {:test} Test33() {
var r0 := haveCommonKSubstring(14, "\U{0012}aa\U{0004}aaa\U{0002}aaa\U{000E}a\U{000C}", "\U{0010}\0aaaaa\U{0006}\U{0008}aaaa\naaaaaaaa");
expect |"\U{0012}aa\U{0004}aaa\U{0002}aaa\U{000E}a\U{000C}"| < 14 || |"\U{0010}\0aaaaa\U{0006}\U{0008}aaaa\naaaaaaaa"| < 14 ==> !r0;
expect haveCommonKSubstringPredicate(14, "\U{0012}aa\U{0004}aaa\U{0002}aaa\U{000E}a\U{000C}", "\U{0010}\0aaaaa\U{0006}\U{0008}aaaa\naaaaaaaa") == r0;
}
method {:test} Test34() {
var r0 := haveCommonKSubstring(30, "\U{0014}aaaaaaaa\U{0004}a\U{0006}aaaaaaaa\n\U{0008}aaaaaa\U{0012}", "a\0aaaaaaaaaaaaa\U{0002}aa\U{000C}a\U{000E}\U{0010}");
expect |"\U{0014}aaaaaaaa\U{0004}a\U{0006}aaaaaaaa\n\U{0008}aaaaaa\U{0012}"| < 30 || |"a\0aaaaaaaaaaaaa\U{0002}aa\U{000C}a\U{000E}\U{0010}"| < 30 ==> !r0;
expect haveCommonKSubstringPredicate(30, "\U{0014}aaaaaaaa\U{0004}a\U{0006}aaaaaaaa\n\U{0008}aaaaaa\U{0012}", "a\0aaaaaaaaaaaaa\U{0002}aa\U{000C}a\U{000E}\U{0010}") == r0;
}
method {:test} Test35() {
var r0 := maxCommonSubstringLength("\U{0006}\0aaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}");
expect r0 <= |"\U{0006}\0aaaaaaaaaaaaaaaaaaa\U{0004}"| && r0 <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}\0aaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}", r0);
}

// REPEAT 4 - TIME: 19.1948779 s

method {:test} Test36() {
var r0 := isPrefix("\U{0004}\0\U{0002}aa\U{0008}", "\U{0004}\0\U{0002}aa\U{0008}aaaaaaaaaaa\U{0006}aaaaaaaaaa");
expect |"\U{0004}\0\U{0002}aa\U{0008}"| > |"\U{0004}\0\U{0002}aa\U{0008}aaaaaaaaaaa\U{0006}aaaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0\U{0002}aa\U{0008}", "\U{0004}\0\U{0002}aa\U{0008}aaaaaaaaaaa\U{0006}aaaaaaaaaa");
}
method {:test} Test37() {
var r0 := isPrefix("\U{0014}aaaaaa\U{0008}a\U{0002}", "a\0aaa\na\U{000E}a\U{0012}a\U{000C}aa\U{0004}aa\U{0006}aaaaa\U{0010}aaaa");
expect |"\U{0014}aaaaaa\U{0008}a\U{0002}"| > |"a\0aaa\na\U{000E}a\U{0012}a\U{000C}aa\U{0004}aa\U{0006}aaaaa\U{0010}aaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0014}aaaaaa\U{0008}a\U{0002}", "a\0aaa\na\U{000E}a\U{0012}a\U{000C}aa\U{0004}aa\U{0006}aaaaa\U{0010}aaaa");
}
method {:test} Test38() {
var r0 := isPrefix("\naaaa\U{0006}\U{0002}a", "\U{0008}\0a\U{0004}");
expect |"\naaaa\U{0006}\U{0002}a"| > |"\U{0008}\0a\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\naaaa\U{0006}\U{0002}a", "\U{0008}\0a\U{0004}");
}
method {:test} Test39() {
var r0 := isSubstring("\U{0006}aaaaaa\0aaa", "\U{0004}aaaaaaaaaaa\U{0002}a\U{0006}aaaaaa\0aaaaaaaa");
expect r0 == isSubstringPredicate("\U{0006}aaaaaa\0aaa", "\U{0004}aaaaaaaaaaa\U{0002}a\U{0006}aaaaaa\0aaaaaaaa");
}
method {:test} Test40() {
var r0 := isSubstring("\U{0006}\0aaa\U{0004}aaaaaaaaaaaaaaaaaaa", "\U{0002}a");
expect r0 == isSubstringPredicate("\U{0006}\0aaa\U{0004}aaaaaaaaaaaaaaaaaaa", "\U{0002}a");
}
method {:test} Test41() {
var r0 := haveCommonKSubstring(16, "\U{0010}a\0aaaaaa\U{0004}aa\U{0008}aaaaaaaaaaaaaaaa\n", "\U{000E}aaaaaa\U{0002}aaa\U{0006}aaaaaaaaaaaaaaaa\U{000C}a");
expect |"\U{0010}a\0aaaaaa\U{0004}aa\U{0008}aaaaaaaaaaaaaaaa\n"| < 16 || |"\U{000E}aaaaaa\U{0002}aaa\U{0006}aaaaaaaaaaaaaaaa\U{000C}a"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "\U{0010}a\0aaaaaa\U{0004}aa\U{0008}aaaaaaaaaaaaaaaa\n", "\U{000E}aaaaaa\U{0002}aaa\U{0006}aaaaaaaaaaaaaaaa\U{000C}a") == r0;
}
method {:test} Test42() {
var r0 := haveCommonKSubstring(16, "\U{0012}aaaaa\U{0002}aa\U{0004}aaaaaaaaaaaaaaaaa\U{000E}aa", "\U{0010}\0aaaaa\U{0006}aaa\U{000C}a\U{0008}\na");
expect |"\U{0012}aaaaa\U{0002}aa\U{0004}aaaaaaaaaaaaaaaaa\U{000E}aa"| < 16 || |"\U{0010}\0aaaaa\U{0006}aaa\U{000C}a\U{0008}\na"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "\U{0012}aaaaa\U{0002}aa\U{0004}aaaaaaaaaaaaaaaaa\U{000E}aa", "\U{0010}\0aaaaa\U{0006}aaa\U{000C}a\U{0008}\na") == r0;
}
method {:test} Test43() {
var r0 := haveCommonKSubstring(31, "\U{0014}\U{0002}aa\U{0004}aaaa\U{0008}aa\U{000C}a\U{0010}", "\U{0012}aaaaaa\U{0006}aaa\U{000E}aaaaaaa\naa\0");
expect |"\U{0014}\U{0002}aa\U{0004}aaaa\U{0008}aa\U{000C}a\U{0010}"| < 31 || |"\U{0012}aaaaaa\U{0006}aaa\U{000E}aaaaaaa\naa\0"| < 31 ==> !r0;
expect haveCommonKSubstringPredicate(31, "\U{0014}\U{0002}aa\U{0004}aaaa\U{0008}aa\U{000C}a\U{0010}", "\U{0012}aaaaaa\U{0006}aaa\U{000E}aaaaaaa\naa\0") == r0;
}
method {:test} Test44() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaa\U{0002}aaaa\U{0006}", "a\0aaaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}a");
expect r0 <= |"aaaaaaaaaaaaaa\U{0002}aaaa\U{0006}"| && r0 <= |"a\0aaaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaa\U{0002}aaaa\U{0006}", "a\0aaaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}a", r0);
}

// REPEAT 5 - TIME: 23.2589936 s

method {:test} Test45() {
var r0 := isPrefix("\U{0002}\0aaa\U{0006}aa\U{000C}\U{0012}\U{000E}\U{0014}aa\U{0016}", "\U{0002}\0aaa\U{0006}aa\U{000C}\U{0012}\U{000E}\U{0014}aa\U{0016}aaaa\na\U{0004}\U{0008}aaaa\U{0018}\U{0010}");
expect |"\U{0002}\0aaa\U{0006}aa\U{000C}\U{0012}\U{000E}\U{0014}aa\U{0016}"| > |"\U{0002}\0aaa\U{0006}aa\U{000C}\U{0012}\U{000E}\U{0014}aa\U{0016}aaaa\na\U{0004}\U{0008}aaaa\U{0018}\U{0010}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0aaa\U{0006}aa\U{000C}\U{0012}\U{000E}\U{0014}aa\U{0016}", "\U{0002}\0aaa\U{0006}aa\U{000C}\U{0012}\U{000E}\U{0014}aa\U{0016}aaaa\na\U{0004}\U{0008}aaaa\U{0018}\U{0010}");
}
method {:test} Test46() {
var r0 := isPrefix("\U{000E}a\0a\U{0008}\U{0006}\U{000C}", "\U{0010}\U{0004}\U{0002}aaaaa\n");
expect |"\U{000E}a\0a\U{0008}\U{0006}\U{000C}"| > |"\U{0010}\U{0004}\U{0002}aaaaa\n"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000E}a\0a\U{0008}\U{0006}\U{000C}", "\U{0010}\U{0004}\U{0002}aaaaa\n");
}
method {:test} Test47() {
var r0 := isPrefix("\U{000C}\0aa\U{0006}\U{0002}a", "\naaa\U{0004}\U{0008}");
expect |"\U{000C}\0aa\U{0006}\U{0002}a"| > |"\naaa\U{0004}\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}\0aa\U{0006}\U{0002}a", "\naaa\U{0004}\U{0008}");
}
method {:test} Test48() {
var r0 := isSubstring("\U{0002}\0a", "\U{0004}aaaaaa\U{0002}\0a");
expect r0 == isSubstringPredicate("\U{0002}\0a", "\U{0004}aaaaaa\U{0002}\0a");
}
method {:test} Test49() {
var r0 := isSubstring("\U{0002}aaa", "\0aa");
expect r0 == isSubstringPredicate("\U{0002}aaa", "\0aa");
}
method {:test} Test50() {
var r0 := haveCommonKSubstring(17, "\U{0014}\U{0002}aaaaaaa\U{0004}a\U{0008}aaaa\U{000E}\U{0010}aaaaaaaaa\U{000C}a", "\U{0012}aaaa\0aaaa\U{0006}\naaaa\U{000E}\U{0010}aaaaaaaaa\U{000C}a");
expect |"\U{0014}\U{0002}aaaaaaa\U{0004}a\U{0008}aaaa\U{000E}\U{0010}aaaaaaaaa\U{000C}a"| < 17 || |"\U{0012}aaaa\0aaaa\U{0006}\naaaa\U{000E}\U{0010}aaaaaaaaa\U{000C}a"| < 17 ==> !r0;
expect haveCommonKSubstringPredicate(17, "\U{0014}\U{0002}aaaaaaa\U{0004}a\U{0008}aaaa\U{000E}\U{0010}aaaaaaaaa\U{000C}a", "\U{0012}aaaa\0aaaa\U{0006}\naaaa\U{000E}\U{0010}aaaaaaaaa\U{000C}a") == r0;
}
method {:test} Test51() {
var r0 := haveCommonKSubstring(17, "\U{0014}\0aaaaaaaaaaaaa\U{000E}aaaaa\U{0002}aaaa\na", "\U{0012}aaaaaa\U{0004}aaa\U{000C}\U{0006}aa\U{0008}\U{0010}");
expect |"\U{0014}\0aaaaaaaaaaaaa\U{000E}aaaaa\U{0002}aaaa\na"| < 17 || |"\U{0012}aaaaaa\U{0004}aaa\U{000C}\U{0006}aa\U{0008}\U{0010}"| < 17 ==> !r0;
expect haveCommonKSubstringPredicate(17, "\U{0014}\0aaaaaaaaaaaaa\U{000E}aaaaa\U{0002}aaaa\na", "\U{0012}aaaaaa\U{0004}aaa\U{000C}\U{0006}aa\U{0008}\U{0010}") == r0;
}
method {:test} Test52() {
var r0 := haveCommonKSubstring(32, "\U{0004}aaaaaaaaa", "\U{0002}aaaaaaaa\0");
expect |"\U{0004}aaaaaaaaa"| < 32 || |"\U{0002}aaaaaaaa\0"| < 32 ==> !r0;
expect haveCommonKSubstringPredicate(32, "\U{0004}aaaaaaaaa", "\U{0002}aaaaaaaa\0") == r0;
}
method {:test} Test53() {
var r0 := maxCommonSubstringLength("\U{0006}aaaaaaaaaaaaa\U{0002}aaaa\U{0008}", "\n\0aaaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <= |"\U{0006}aaaaaaaaaaaaa\U{0002}aaaa\U{0008}"| && r0 <= |"\n\0aaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}aaaaaaaaaaaaa\U{0002}aaaa\U{0008}", "\n\0aaaaaaaaaaaaaaaaaaa\U{0004}", r0);
}

// REPEAT 6 - TIME: 27.5863812 s

method {:test} Test54() {
var r0 := isPrefix("\U{0004}\U{0002}aa\U{0006}aaaaa", "\U{0004}\U{0002}aa\U{0006}aaaaa\U{0008}aaaaaaaaaaaaaaaa\0");
expect |"\U{0004}\U{0002}aa\U{0006}aaaaa"| > |"\U{0004}\U{0002}aa\U{0006}aaaaa\U{0008}aaaaaaaaaaaaaaaa\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\U{0002}aa\U{0006}aaaaa", "\U{0004}\U{0002}aa\U{0006}aaaaa\U{0008}aaaaaaaaaaaaaaaa\0");
}
method {:test} Test55() {
var r0 := isPrefix("a\0a\U{0008}\U{0004}\naaaaa\U{0016}a\U{0012}\U{0014}\U{0018}", "\U{001A}\U{0002}aaaaa\U{000E}a\U{0006}aa\U{0010}\U{000C}aa");
expect |"a\0a\U{0008}\U{0004}\naaaaa\U{0016}a\U{0012}\U{0014}\U{0018}"| > |"\U{001A}\U{0002}aaaaa\U{000E}a\U{0006}aa\U{0010}\U{000C}aa"| ==> !r0;
expect r0 == isPrefixPredicate("a\0a\U{0008}\U{0004}\naaaaa\U{0016}a\U{0012}\U{0014}\U{0018}", "\U{001A}\U{0002}aaaaa\U{000E}a\U{0006}aa\U{0010}\U{000C}aa");
}
method {:test} Test56() {
var r0 := isPrefix("\U{000E}\0aaaa\U{000C}\U{0006}aa\U{0004}", "\U{0010}aa\U{0008}a\na\U{0002}");
expect |"\U{000E}\0aaaa\U{000C}\U{0006}aa\U{0004}"| > |"\U{0010}aa\U{0008}a\na\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000E}\0aaaa\U{000C}\U{0006}aa\U{0004}", "\U{0010}aa\U{0008}a\na\U{0002}");
}
method {:test} Test57() {
var r0 := isSubstring("\U{000E}aaaa\U{0006}aaaaa\0a", "\U{0004}aaaa\U{0002}aaa\U{0008}\n\U{000C}aaa\U{000E}aaaa\U{0006}aaaaa\0aa");
expect r0 == isSubstringPredicate("\U{000E}aaaa\U{0006}aaaaa\0a", "\U{0004}aaaa\U{0002}aaa\U{0008}\n\U{000C}aaa\U{000E}aaaa\U{0006}aaaaa\0aa");
}
method {:test} Test58() {
var r0 := isSubstring("\U{0004}\0aaaa\naaa\U{000C}aa\U{0014}\U{0016}", "\U{0018}\U{0002}a\U{0006}aaaaa\U{000E}\U{0010}\U{0008}\U{0012}a");
expect r0 == isSubstringPredicate("\U{0004}\0aaaa\naaa\U{000C}aa\U{0014}\U{0016}", "\U{0018}\U{0002}a\U{0006}aaaaa\U{000E}\U{0010}\U{0008}\U{0012}a");
}
method {:test} Test59() {
var r0 := haveCommonKSubstring(18, "a\U{0002}aaaaaaaaaaaaaaaaaaa\naa\U{000E}aa", "\U{0010}\0aaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaa\U{0008}\U{000C}");
expect |"a\U{0002}aaaaaaaaaaaaaaaaaaa\naa\U{000E}aa"| < 18 || |"\U{0010}\0aaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaa\U{0008}\U{000C}"| < 18 ==> !r0;
expect haveCommonKSubstringPredicate(18, "a\U{0002}aaaaaaaaaaaaaaaaaaa\naa\U{000E}aa", "\U{0010}\0aaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaa\U{0008}\U{000C}") == r0;
}
method {:test} Test60() {
var r0 := haveCommonKSubstring(21, "\U{0014}aaaaaaaaaaaaaaaaaa\0aaaa\U{000E}aaa\U{0012}", "\U{0016}aaaaaaaaaaaaaaa\U{0002}\U{0004}a\U{0006}a\U{0008}\U{000C}a\naaaa\U{0010}");
expect |"\U{0014}aaaaaaaaaaaaaaaaaa\0aaaa\U{000E}aaa\U{0012}"| < 21 || |"\U{0016}aaaaaaaaaaaaaaa\U{0002}\U{0004}a\U{0006}a\U{0008}\U{000C}a\naaaa\U{0010}"| < 21 ==> !r0;
expect haveCommonKSubstringPredicate(21, "\U{0014}aaaaaaaaaaaaaaaaaa\0aaaa\U{000E}aaa\U{0012}", "\U{0016}aaaaaaaaaaaaaaa\U{0002}\U{0004}a\U{0006}a\U{0008}\U{000C}a\naaaa\U{0010}") == r0;
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(33, "\U{0014}aaaaaaaaaaaaaa\U{0002}aaaaaaa\0\U{0010}aaa", "\U{0016}aaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}\U{000E}aaa\n\U{0012}\U{0006}");
expect |"\U{0014}aaaaaaaaaaaaaa\U{0002}aaaaaaa\0\U{0010}aaa"| < 33 || |"\U{0016}aaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}\U{000E}aaa\n\U{0012}\U{0006}"| < 33 ==> !r0;
expect haveCommonKSubstringPredicate(33, "\U{0014}aaaaaaaaaaaaaa\U{0002}aaaaaaa\0\U{0010}aaa", "\U{0016}aaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}\U{000E}aaa\n\U{0012}\U{0006}") == r0;
}
method {:test} Test62() {
var r0 := maxCommonSubstringLength("\U{0004}a\U{0002}aaaaaaaaaaaaaaa\U{0006}a\U{0008}", "\n\0a");
expect r0 <= |"\U{0004}a\U{0002}aaaaaaaaaaaaaaa\U{0006}a\U{0008}"| && r0 <= |"\n\0a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}a\U{0002}aaaaaaaaaaaaaaa\U{0006}a\U{0008}", "\n\0a", r0);
}

// REPEAT 7 - TIME: 31.8922205 s

method {:test} Test63() {
var r0 := isPrefix("\U{0008}a\0a\U{0004}", "\U{0008}a\0a\U{0004}\na\U{0002}aaaa\U{0006}a");
expect |"\U{0008}a\0a\U{0004}"| > |"\U{0008}a\0a\U{0004}\na\U{0002}aaaa\U{0006}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}a\0a\U{0004}", "\U{0008}a\0a\U{0004}\na\U{0002}aaaa\U{0006}a");
}
method {:test} Test64() {
var r0 := isPrefix("a\0aaa\U{0008}a\U{000C}a\U{0016}a\U{001A}\U{0012}\U{0018}\U{0014}\U{0004}\U{001C}", " \U{0002}aaaaa\naa\U{0006}a\U{000E}aa\U{0010}\U{001E}");
expect |"a\0aaa\U{0008}a\U{000C}a\U{0016}a\U{001A}\U{0012}\U{0018}\U{0014}\U{0004}\U{001C}"| > |" \U{0002}aaaaa\naa\U{0006}a\U{000E}aa\U{0010}\U{001E}"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaa\U{0008}a\U{000C}a\U{0016}a\U{001A}\U{0012}\U{0018}\U{0014}\U{0004}\U{001C}", " \U{0002}aaaaa\naa\U{0006}a\U{000E}aa\U{0010}\U{001E}");
}
method {:test} Test65() {
var r0 := isPrefix("\U{0012}aa\U{0002}aaaaa\U{0006}\U{0008}aaaaa\U{000E}", "\U{0010}\0aaa\U{000C}a\U{0004}\na");
expect |"\U{0012}aa\U{0002}aaaaa\U{0006}\U{0008}aaaaa\U{000E}"| > |"\U{0010}\0aaa\U{000C}a\U{0004}\na"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0012}aa\U{0002}aaaaa\U{0006}\U{0008}aaaaa\U{000E}", "\U{0010}\0aaa\U{000C}a\U{0004}\na");
}
method {:test} Test66() {
var r0 := isSubstring("\U{0012}\0aaa\naaa\U{0002}\U{0008}\U{0010}", "\U{0004}aaaaaaaa\U{000C}\U{0006}\U{000E}a\U{0012}\0aaa\naaa\U{0002}\U{0008}\U{0010}aa\U{0014}");
expect r0 == isSubstringPredicate("\U{0012}\0aaa\naaa\U{0002}\U{0008}\U{0010}", "\U{0004}aaaaaaaa\U{000C}\U{0006}\U{000E}a\U{0012}\0aaa\naaa\U{0002}\U{0008}\U{0010}aa\U{0014}");
}
method {:test} Test67() {
var r0 := isSubstring("\U{0002}aaaaaaaaaaa", "\0aaaaaaaa");
expect r0 == isSubstringPredicate("\U{0002}aaaaaaaaaaa", "\0aaaaaaaa");
}
method {:test} Test68() {
var r0 := haveCommonKSubstring(24, "\0aaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaaa");
expect |"\0aaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaa"| < 24 || |"\U{0002}aaaaaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaaa"| < 24 ==> !r0;
expect haveCommonKSubstringPredicate(24, "\0aaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaa\U{0004}a\U{0006}aaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test69() {
var r0 := haveCommonKSubstring(27, "\U{000C}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\0\U{0008}", "\U{000E}aaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0006}aaaa\n");
expect |"\U{000C}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\0\U{0008}"| < 27 || |"\U{000E}aaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0006}aaaa\n"| < 27 ==> !r0;
expect haveCommonKSubstringPredicate(27, "\U{000C}aaaaaaaaaaaaaa\U{0002}aaaaaaaaaa\0\U{0008}", "\U{000E}aaaaaaaaaaaaaaaa\U{0004}aaaaa\U{0006}aaaa\n") == r0;
}
method {:test} Test70() {
var r0 := haveCommonKSubstring(34, "\U{0004}aaaaaaaaa\0aa", "\U{0002}aaaaaaaaaaa");
expect |"\U{0004}aaaaaaaaa\0aa"| < 34 || |"\U{0002}aaaaaaaaaaa"| < 34 ==> !r0;
expect haveCommonKSubstringPredicate(34, "\U{0004}aaaaaaaaa\0aa", "\U{0002}aaaaaaaaaaa") == r0;
}
method {:test} Test71() {
var r0 := maxCommonSubstringLength("\U{0006}aaaaaaaaaa\U{0002}aaaaaaaa\U{0008}a\n", "\U{0010}\0aaaaaaaaaaaaaaaaaaaaa\U{000C}\U{0004}\U{000E}");
expect r0 <= |"\U{0006}aaaaaaaaaa\U{0002}aaaaaaaa\U{0008}a\n"| && r0 <= |"\U{0010}\0aaaaaaaaaaaaaaaaaaaaa\U{000C}\U{0004}\U{000E}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}aaaaaaaaaa\U{0002}aaaaaaaa\U{0008}a\n", "\U{0010}\0aaaaaaaaaaaaaaaaaaaaa\U{000C}\U{0004}\U{000E}", r0);
}

// REPEAT 8 - TIME: 37.0039912 s

method {:test} Test72() {
var r0 := isPrefix("aaaaaaa\U{0008}aaa\U{000C}a\U{0006}a\U{000E}\U{0012}aa\naa\U{0010}\0a\U{0002}a", "aaaaaaa\U{0008}aaa\U{000C}a\U{0006}a\U{000E}\U{0012}aa\naa\U{0010}\0a\U{0002}a\U{0004}a\U{0014}");
expect |"aaaaaaa\U{0008}aaa\U{000C}a\U{0006}a\U{000E}\U{0012}aa\naa\U{0010}\0a\U{0002}a"| > |"aaaaaaa\U{0008}aaa\U{000C}a\U{0006}a\U{000E}\U{0012}aa\naa\U{0010}\0a\U{0002}a\U{0004}a\U{0014}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaa\U{0008}aaa\U{000C}a\U{0006}a\U{000E}\U{0012}aa\naa\U{0010}\0a\U{0002}a", "aaaaaaa\U{0008}aaa\U{000C}a\U{0006}a\U{000E}\U{0012}aa\naa\U{0010}\0a\U{0002}a\U{0004}a\U{0014}");
}
method {:test} Test73() {
var r0 := isPrefix("\U{0012}\U{0006}aa\U{000E}aaa\U{000C}\U{0008}aaa\0aaaa", "\U{0010}\U{0004}aaaaaaaa\naa\U{0002}aaaaaaaaaaaaaaaa");
expect |"\U{0012}\U{0006}aa\U{000E}aaa\U{000C}\U{0008}aaa\0aaaa"| > |"\U{0010}\U{0004}aaaaaaaa\naa\U{0002}aaaaaaaaaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0012}\U{0006}aa\U{000E}aaa\U{000C}\U{0008}aaa\0aaaa", "\U{0010}\U{0004}aaaaaaaa\naa\U{0002}aaaaaaaaaaaaaaaa");
}
method {:test} Test74() {
var r0 := isPrefix("\U{000E}aaaaa\naaaaaaaaaaaa", "\U{000C}\0aaa\U{0008}aa\U{0006}\U{0002}\U{0004}aaaaaaa");
expect |"\U{000E}aaaaa\naaaaaaaaaaaa"| > |"\U{000C}\0aaa\U{0008}aa\U{0006}\U{0002}\U{0004}aaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000E}aaaaa\naaaaaaaaaaaa", "\U{000C}\0aaa\U{0008}aa\U{0006}\U{0002}\U{0004}aaaaaaa");
}
method {:test} Test75() {
var r0 := isSubstring("\U{000E}\0aaaaa\U{0004}aaaa\U{0008}\n", "\U{0010}aaa\U{0002}aaaaaa\U{0006}a\U{000C}\U{000E}\0aaaaa\U{0004}aaaa\U{0008}\n");
expect r0 == isSubstringPredicate("\U{000E}\0aaaaa\U{0004}aaaa\U{0008}\n", "\U{0010}aaa\U{0002}aaaaaa\U{0006}a\U{000C}\U{000E}\0aaaaa\U{0004}aaaa\U{0008}\n");
}
method {:test} Test76() {
var r0 := isSubstring("aaaaa\naaa\U{0008}aaaaaaa\U{0014}aaa\U{0012}\U{0016}aa\U{0018}", "\U{001A}\0aaa\U{0002}aaa\U{000E}a\U{000C}\U{0004}\U{0010}\U{0006}");
expect r0 == isSubstringPredicate("aaaaa\naaa\U{0008}aaaaaaa\U{0014}aaa\U{0012}\U{0016}aa\U{0018}", "\U{001A}\0aaa\U{0002}aaa\U{000E}a\U{000C}\U{0004}\U{0010}\U{0006}");
}
method {:test} Test77() {
var r0 := haveCommonKSubstring(29, "\0aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa"| < 29 || |"\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\0aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa") == r0;
}
method {:test} Test78() {
var r0 := haveCommonKSubstring(28, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 28 || |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test79() {
var r0 := haveCommonKSubstring(35, "\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| < 35 || |"\U{0002}aaaaaaaaaaaa"| < 35 ==> !r0;
expect haveCommonKSubstringPredicate(35, "\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaa") == r0;
}
method {:test} Test80() {
var r0 := maxCommonSubstringLength("\n\0aa\U{0004}aaaaaaaaaaaaaaa\U{0008}\U{000C}\U{000E}\U{0012}", "\U{0016}aa\U{0006}aaaaaaaaaaaaaaaaaaa\U{0010}\U{0002}\U{0014}");
expect r0 <= |"\n\0aa\U{0004}aaaaaaaaaaaaaaa\U{0008}\U{000C}\U{000E}\U{0012}"| && r0 <= |"\U{0016}aa\U{0006}aaaaaaaaaaaaaaaaaaa\U{0010}\U{0002}\U{0014}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\n\0aa\U{0004}aaaaaaaaaaaaaaa\U{0008}\U{000C}\U{000E}\U{0012}", "\U{0016}aa\U{0006}aaaaaaaaaaaaaaaaaaa\U{0010}\U{0002}\U{0014}", r0);
}

// REPEAT 9 - TIME: 42.0259872 s

method {:test} Test81() {
var r0 := isPrefix("\U{0006}aaaa\0", "\U{0006}aaaa\0\U{0008}a\U{0002}aaaa\U{0004}a");
expect |"\U{0006}aaaa\0"| > |"\U{0006}aaaa\0\U{0008}a\U{0002}aaaa\U{0004}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}aaaa\0", "\U{0006}aaaa\0\U{0008}a\U{0002}aaaa\U{0004}a");
}
method {:test} Test82() {
var r0 := isPrefix("\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa\0", "\naaaa\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0002}");
expect |"\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa\0"| > |"\naaaa\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}aaaaaaaaaaaa\U{0006}aaaaaaaa\U{0008}aaa\0", "\naaaa\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0002}");
}
method {:test} Test83() {
var r0 := isPrefix("aaaaa\0aaaaa\U{0006}aaa\U{0008}aaaaaaa\U{0010}\U{000C}aa\U{0018}\U{0012}a", "\U{001A}aaaaaaaa\U{0004}aaaaaaa\U{0014}a\naaa\U{0002}\U{0016}aa\U{000E}a");
expect |"aaaaa\0aaaaa\U{0006}aaa\U{0008}aaaaaaa\U{0010}\U{000C}aa\U{0018}\U{0012}a"| > |"\U{001A}aaaaaaaa\U{0004}aaaaaaa\U{0014}a\naaa\U{0002}\U{0016}aa\U{000E}a"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaa\0aaaaa\U{0006}aaa\U{0008}aaaaaaa\U{0010}\U{000C}aa\U{0018}\U{0012}a", "\U{001A}aaaaaaaa\U{0004}aaaaaaa\U{0014}a\naaa\U{0002}\U{0016}aa\U{000E}a");
}
method {:test} Test84() {
var r0 := isSubstring("\U{0004}a", "\U{0002}\0aaaaaa\U{0004}aaaa");
expect r0 == isSubstringPredicate("\U{0004}a", "\U{0002}\0aaaaaa\U{0004}aaaa");
}
method {:test} Test85() {
var r0 := isSubstring("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test86() {
var r0 := haveCommonKSubstring(25, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa"| < 25 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| < 25 ==> !r0;
expect haveCommonKSubstringPredicate(25, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test87() {
var r0 := haveCommonKSubstring(25, "\naaaaaaaaaaaaaa\0aaaaaaaaa", "\U{0008}aaaaaaaaaaaaaaaa\U{0004}aaa\U{0002}a\U{0006}aaa");
expect |"\naaaaaaaaaaaaaa\0aaaaaaaaa"| < 25 || |"\U{0008}aaaaaaaaaaaaaaaa\U{0004}aaa\U{0002}a\U{0006}aaa"| < 25 ==> !r0;
expect haveCommonKSubstringPredicate(25, "\naaaaaaaaaaaaaa\0aaaaaaaaa", "\U{0008}aaaaaaaaaaaaaaaa\U{0004}aaa\U{0002}a\U{0006}aaa") == r0;
}
method {:test} Test88() {
var r0 := haveCommonKSubstring(36, "aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaa"| < 36 || |"\U{0004}aaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaa"| < 36 ==> !r0;
expect haveCommonKSubstringPredicate(36, "aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaa\0\U{0002}aaaaaaaaa") == r0;
}
method {:test} Test89() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}aa\U{0008}\U{0006}", "\U{000E}aaaaaaaaaaaaaaaaaaaa\0a\na\U{000C}aa");
expect r0 <= |"aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}aa\U{0008}\U{0006}"| && r0 <= |"\U{000E}aaaaaaaaaaaaaaaaaaaa\0a\na\U{000C}aa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}aa\U{0008}\U{0006}", "\U{000E}aaaaaaaaaaaaaaaaaaaa\0a\na\U{000C}aa", r0);
}

// REPEAT 10 - TIME: 47.5429408 s

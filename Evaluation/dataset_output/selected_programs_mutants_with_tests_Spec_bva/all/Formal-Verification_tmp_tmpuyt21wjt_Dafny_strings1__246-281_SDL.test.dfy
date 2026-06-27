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
var r0 := isPrefix("", "a");
expect |""| > |"a"| ==> !r0;
expect r0 == isPrefixPredicate("", "a");
}
method {:test} Test3() {
var r0 := isPrefix("aaaaaaaaaaa", "aaaaaaaaaaa");
expect |"aaaaaaaaaaa"| > |"aaaaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaaaa", "aaaaaaaaaaa");
}
method {:test} Test4() {
var r0 := isPrefix("", "");
expect |""| > |""| ==> !r0;
expect r0 == isPrefixPredicate("", "");
}
method {:test} Test6() {
var r0 := isPrefix("a", "aa");
expect |"a"| > |"aa"| ==> !r0;
expect r0 == isPrefixPredicate("a", "aa");
}
method {:test} Test11() {
var r0 := isPrefix("aaaaaaaa\0", "aaaaaaaa\U{0002}");
expect |"aaaaaaaa\0"| > |"aaaaaaaa\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaa\0", "aaaaaaaa\U{0002}");
}
method {:test} Test12() {
var r0 := isPrefix("\U{0002}", "\0");
expect |"\U{0002}"| > |"\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}", "\0");
}
method {:test} Test13() {
var r0 := isPrefix("aaaaaaaa\0aa", "aaaaaaaa\U{0002}aa");
expect |"aaaaaaaa\0aa"| > |"aaaaaaaa\U{0002}aa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaa\0aa", "aaaaaaaa\U{0002}aa");
}
method {:test} Test14() {
var r0 := isPrefix("\0", "\U{0002}");
expect |"\0"| > |"\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\0", "\U{0002}");
}
method {:test} Test15() {
var r0 := isPrefix("aaaaaaaaa\0", "aaaaaaaaa\U{0002}a");
expect |"aaaaaaaaa\0"| > |"aaaaaaaaa\U{0002}a"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaa\0", "aaaaaaaaa\U{0002}a");
}
method {:test} Test20() {
var r0 := isPrefix("aaaaaaa", "aaaaaa");
expect |"aaaaaaa"| > |"aaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaa", "aaaaaa");
}
method {:test} Test21() {
var r0 := isPrefix("a", "");
expect |"a"| > |""| ==> !r0;
expect r0 == isPrefixPredicate("a", "");
}
method {:test} Test22() {
var r0 := isPrefix("aaaaaaaaaaa", "a");
expect |"aaaaaaaaaaa"| > |"a"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaaaa", "a");
}
method {:test} Test25() {
var r0 := isPrefix("aaaaaaaaaaaaa", "aaaaaaaaaaaa");
expect |"aaaaaaaaaaaaa"| > |"aaaaaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaaaaaa", "aaaaaaaaaaaa");
}
method {:test} Test30() {
var r0 := isSubstring("a", "aaaaaaaaaaa");
expect r0 == isSubstringPredicate("a", "aaaaaaaaaaa");
}
method {:test} Test31() {
var r0 := isSubstring("", "aa");
expect r0 == isSubstringPredicate("", "aa");
}
method {:test} Test33() {
var r0 := isSubstring("aaaaaaaaaaaa", "aaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("aaaaaaaaaaaa", "aaaaaaaaaaaaa");
}
method {:test} Test34() {
var r0 := isSubstring("", "");
expect r0 == isSubstringPredicate("", "");
}
method {:test} Test35() {
var r0 := isSubstring("", "a");
expect r0 == isSubstringPredicate("", "a");
}
method {:test} Test36() {
var r0 := isSubstring("a", "aa");
expect r0 == isSubstringPredicate("a", "aa");
}
method {:test} Test40() {
var r0 := isSubstring("aaaaaaaaaa", "aaaaaaaaaaa");
expect r0 == isSubstringPredicate("aaaaaaaaaa", "aaaaaaaaaaa");
}
method {:test} Test41() {
var r0 := isSubstring("aa", "a");
expect r0 == isSubstringPredicate("aa", "a");
}
method {:test} Test43() {
var r0 := isSubstring("a", "");
expect r0 == isSubstringPredicate("a", "");
}
method {:test} Test47() {
var r0 := isSubstring("aaa", "aa");
expect r0 == isSubstringPredicate("aaa", "aa");
}
method {:test} Test52() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaa", "aaaaaaa");
expect |"aaaaaaaaaaa"| < 1 || |"aaaaaaa"| < 1 ==> !r0;
expect haveCommonKSubstringPredicate(1, "aaaaaaaaaaa", "aaaaaaa") == r0;
}
method {:test} Test53() {
var r0 := haveCommonKSubstring(0, "", "aa");
expect |""| < 0 || |"aa"| < 0 ==> !r0;
expect haveCommonKSubstringPredicate(0, "", "aa") == r0;
}
method {:test} Test54() {
var r0 := haveCommonKSubstring(1, "a", "aaaaaaaaaaa");
expect |"a"| < 1 || |"aaaaaaaaaaa"| < 1 ==> !r0;
expect haveCommonKSubstringPredicate(1, "a", "aaaaaaaaaaa") == r0;
}
method {:test} Test56() {
var r0 := haveCommonKSubstring(0, "a", "");
expect |"a"| < 0 || |""| < 0 ==> !r0;
expect haveCommonKSubstringPredicate(0, "a", "") == r0;
}
method {:test} Test57() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaa", "a");
expect |"aaaaaaaaaaa"| < 1 || |"a"| < 1 ==> !r0;
expect haveCommonKSubstringPredicate(1, "aaaaaaaaaaa", "a") == r0;
}
method {:test} Test58() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaa", "aa");
expect |"aaaaaaaaaaa"| < 1 || |"aa"| < 1 ==> !r0;
expect haveCommonKSubstringPredicate(1, "aaaaaaaaaaa", "aa") == r0;
}
method {:test} Test63() {
var r0 := haveCommonKSubstring(0, "a", "a");
expect |"a"| < 0 || |"a"| < 0 ==> !r0;
expect haveCommonKSubstringPredicate(0, "a", "a") == r0;
}
method {:test} Test64() {
var r0 := haveCommonKSubstring(0, "", "a");
expect |""| < 0 || |"a"| < 0 ==> !r0;
expect haveCommonKSubstringPredicate(0, "", "a") == r0;
}
method {:test} Test66() {
var r0 := haveCommonKSubstring(0, "aa", "a");
expect |"aa"| < 0 || |"a"| < 0 ==> !r0;
expect haveCommonKSubstringPredicate(0, "aa", "a") == r0;
}
method {:test} Test69() {
var r0 := haveCommonKSubstring(0, "a", "aa");
expect |"a"| < 0 || |"aa"| < 0 ==> !r0;
expect haveCommonKSubstringPredicate(0, "a", "aa") == r0;
}
method {:test} Test74() {
var r0 := haveCommonKSubstring(10, "aaaaaaaaa", "");
expect |"aaaaaaaaa"| < 10 || |""| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "aaaaaaaaa", "") == r0;
}
method {:test} Test75() {
var r0 := haveCommonKSubstring(100, "a", "");
expect |"a"| < 100 || |""| < 100 ==> !r0;
expect haveCommonKSubstringPredicate(100, "a", "") == r0;
}
method {:test} Test76() {
var r0 := haveCommonKSubstring(1, "", "");
expect |""| < 1 || |""| < 1 ==> !r0;
expect haveCommonKSubstringPredicate(1, "", "") == r0;
}
method {:test} Test77() {
var r0 := haveCommonKSubstring(40, "a", "");
expect |"a"| < 40 || |""| < 40 ==> !r0;
expect haveCommonKSubstringPredicate(40, "a", "") == r0;
}
method {:test} Test78() {
var r0 := haveCommonKSubstring(12, "aaaaaaaaaaa", "");
expect |"aaaaaaaaaaa"| < 12 || |""| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "aaaaaaaaaaa", "") == r0;
}
method {:test} Test80() {
var r0 := haveCommonKSubstring(10, "aaaaaaaaa", "a");
expect |"aaaaaaaaa"| < 10 || |"a"| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "aaaaaaaaa", "a") == r0;
}
method {:test} Test81() {
var r0 := haveCommonKSubstring(10, "aaaaaaaaa", "aa");
expect |"aaaaaaaaa"| < 10 || |"aa"| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "aaaaaaaaa", "aa") == r0;
}
method {:test} Test82() {
var r0 := haveCommonKSubstring(10, "", "aaaaaaaaa");
expect |""| < 10 || |"aaaaaaaaa"| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "", "aaaaaaaaa") == r0;
}
method {:test} Test86() {
var r0 := maxCommonSubstringLength("a", "a");
expect r0 <= |"a"| && r0 <= |"a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a", "a", r0);
}
method {:test} Test87() {
var r0 := maxCommonSubstringLength("", "a");
expect r0 <= |""| && r0 <= |"a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("", "a", r0);
}
method {:test} Test89() {
var r0 := maxCommonSubstringLength("aa", "a");
expect r0 <= |"aa"| && r0 <= |"a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aa", "a", r0);
}
method {:test} Test90() {
var r0 := maxCommonSubstringLength("a", "");
expect r0 <= |"a"| && r0 <= |""|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a", "", r0);
}
method {:test} Test92() {
var r0 := maxCommonSubstringLength("a", "aa");
expect r0 <= |"a"| && r0 <= |"aa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a", "aa", r0);
}

// REPEAT 1 - TIME: 52.2294547 s

method {:test} Test97() {
var r0 := isPrefix("\U{0004}\0a\U{0002}aa\U{0006}\U{0008}aa", "\U{0004}\0a\U{0002}aa\U{0006}\U{0008}aa");
expect |"\U{0004}\0a\U{0002}aa\U{0006}\U{0008}aa"| > |"\U{0004}\0a\U{0002}aa\U{0006}\U{0008}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0a\U{0002}aa\U{0006}\U{0008}aa", "\U{0004}\0a\U{0002}aa\U{0006}\U{0008}aa");
}
method {:test} Test98() {
var r0 := isPrefix("\U{0008}\U{0004}aaaa\0a", "\naaaaa\U{0002}aaa\U{0006}aa");
expect |"\U{0008}\U{0004}aaaa\0a"| > |"\naaaaa\U{0002}aaa\U{0006}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}\U{0004}aaaa\0a", "\naaaaa\U{0002}aaa\U{0006}aa");
}
method {:test} Test99() {
var r0 := isPrefix("\U{0006}aaaaaaaaaa\0a", "\U{0004}\U{0002}");
expect |"\U{0006}aaaaaaaaaa\0a"| > |"\U{0004}\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}aaaaaaaaaa\0a", "\U{0004}\U{0002}");
}
method {:test} Test100() {
var r0 := isSubstring("\U{0008}a\0\U{0006}", "\U{0004}\U{0002}\U{0008}a\0\U{0006}");
expect r0 == isSubstringPredicate("\U{0008}a\0\U{0006}", "\U{0004}\U{0002}\U{0008}a\0\U{0006}");
}
method {:test} Test101() {
var r0 := isSubstring("\U{0004}aaaaaaaaa\U{0006}", "\U{0008}\0\U{0002}");
expect r0 == isSubstringPredicate("\U{0004}aaaaaaaaa\U{0006}", "\U{0008}\0\U{0002}");
}
method {:test} Test102() {
var r0 := haveCommonKSubstring(13, "\U{0002}aaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaa"| < 13 || |"\0aaaaaaaaaaaaaaaaaaa"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "\U{0002}aaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test103() {
var r0 := haveCommonKSubstring(13, "\U{0008}\0aaaaaaaaaaa", "\U{0004}aaaaaa\U{0006}a\U{0002}aaa");
expect |"\U{0008}\0aaaaaaaaaaa"| < 13 || |"\U{0004}aaaaaa\U{0006}a\U{0002}aaa"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "\U{0008}\0aaaaaaaaaaa", "\U{0004}aaaaaa\U{0006}a\U{0002}aaa") == r0;
}
method {:test} Test104() {
var r0 := haveCommonKSubstring(101, "\n\U{0002}aaaaa\U{0008}a\0", "\U{0006}aaa\U{0004}aaaaaaaaaa");
expect |"\n\U{0002}aaaaa\U{0008}a\0"| < 101 || |"\U{0006}aaa\U{0004}aaaaaaaaaa"| < 101 ==> !r0;
expect haveCommonKSubstringPredicate(101, "\n\U{0002}aaaaa\U{0008}a\0", "\U{0006}aaa\U{0004}aaaaaaaaaa") == r0;
}
method {:test} Test105() {
var r0 := maxCommonSubstringLength("a\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}", "aaaaaaaaaaa\0aaaa\U{0004}");
expect r0 <= |"a\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 <= |"aaaaaaaaaaa\0aaaa\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}", "aaaaaaaaaaa\0aaaa\U{0004}", r0);
}

// REPEAT 2 - TIME: 56.5683705 s

method {:test} Test106() {
var r0 := isPrefix("\U{0006}\0\U{0004}aaaa\na\U{0008}a", "\U{0006}\0\U{0004}aaaa\na\U{0008}a\U{0002}");
expect |"\U{0006}\0\U{0004}aaaa\na\U{0008}a"| > |"\U{0006}\0\U{0004}aaaa\na\U{0008}a\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\0\U{0004}aaaa\na\U{0008}a", "\U{0006}\0\U{0004}aaaa\na\U{0008}a\U{0002}");
}
method {:test} Test107() {
var r0 := isPrefix("\U{0010}\0a\U{0004}aaa\U{0008}aaa\U{000C}", "\U{000E}\U{0002}aaaaaaa\na\U{0006}");
expect |"\U{0010}\0a\U{0004}aaa\U{0008}aaa\U{000C}"| > |"\U{000E}\U{0002}aaaaaaa\na\U{0006}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0010}\0a\U{0004}aaa\U{0008}aaa\U{000C}", "\U{000E}\U{0002}aaaaaaa\na\U{0006}");
}
method {:test} Test108() {
var r0 := isPrefix("\U{000C}a\U{0002}\U{0004}aaa\U{0008}a\na", "\U{000E}\0aaaaa\U{0006}");
expect |"\U{000C}a\U{0002}\U{0004}aaa\U{0008}a\na"| > |"\U{000E}\0aaaaa\U{0006}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}a\U{0002}\U{0004}aaa\U{0008}a\na", "\U{000E}\0aaaaa\U{0006}");
}
method {:test} Test109() {
var r0 := isSubstring("\U{0008}\U{0002}\0\U{000C}\n", "\U{0006}aaaaaaaaaaaa\U{0004}aa\U{0008}\U{0002}\0\U{000C}\n");
expect r0 == isSubstringPredicate("\U{0008}\U{0002}\0\U{000C}\n", "\U{0006}aaaaaaaaaaaa\U{0004}aa\U{0008}\U{0002}\0\U{000C}\n");
}
method {:test} Test110() {
var r0 := isSubstring("\U{000E}aa\U{0004}a\U{000C}aa\U{0008}a\0", "\n\U{0002}\U{0006}");
expect r0 == isSubstringPredicate("\U{000E}aa\U{0004}a\U{000C}aa\U{0008}a\0", "\n\U{0002}\U{0006}");
}
method {:test} Test111() {
var r0 := haveCommonKSubstring(14, "\U{000C}aa\U{0002}aaaa\U{0004}\naaaaaaaaaaaaaa", "\U{0008}\0a\U{0006}aaaaaaaaaaaaaa");
expect |"\U{000C}aa\U{0002}aaaa\U{0004}\naaaaaaaaaaaaaa"| < 14 || |"\U{0008}\0a\U{0006}aaaaaaaaaaaaaa"| < 14 ==> !r0;
expect haveCommonKSubstringPredicate(14, "\U{000C}aa\U{0002}aaaa\U{0004}\naaaaaaaaaaaaaa", "\U{0008}\0a\U{0006}aaaaaaaaaaaaaa") == r0;
}
method {:test} Test112() {
var r0 := haveCommonKSubstring(14, "\U{000C}aa\U{0004}aaaaa\U{0008}aa\na", "\U{0002}\0aaaaa\U{0006}aaaaaa");
expect |"\U{000C}aa\U{0004}aaaaa\U{0008}aa\na"| < 14 || |"\U{0002}\0aaaaa\U{0006}aaaaaa"| < 14 ==> !r0;
expect haveCommonKSubstringPredicate(14, "\U{000C}aa\U{0004}aaaaa\U{0008}aa\na", "\U{0002}\0aaaaa\U{0006}aaaaaa") == r0;
}
method {:test} Test113() {
var r0 := haveCommonKSubstring(102, "\U{000C}\U{0002}\U{0008}", "\na\U{0006}aaaaaaa\U{0004}aaaa\0");
expect |"\U{000C}\U{0002}\U{0008}"| < 102 || |"\na\U{0006}aaaaaaa\U{0004}aaaa\0"| < 102 ==> !r0;
expect haveCommonKSubstringPredicate(102, "\U{000C}\U{0002}\U{0008}", "\na\U{0006}aaaaaaa\U{0004}aaaa\0") == r0;
}
method {:test} Test114() {
var r0 := maxCommonSubstringLength("\U{0002}\0", "\U{0006}a\U{0004}");
expect r0 <= |"\U{0002}\0"| && r0 <= |"\U{0006}a\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}\0", "\U{0006}a\U{0004}", r0);
}

// REPEAT 3 - TIME: 61.7728887 s

method {:test} Test115() {
var r0 := isPrefix("\U{0008}\0a\U{000E}a\U{0002}a\U{0006}\U{000C}\naaaa\U{0004}aaaaaaaaaaaaa", "\U{0008}\0a\U{000E}a\U{0002}a\U{0006}\U{000C}\naaaa\U{0004}aaaaaaaaaaaaa");
expect |"\U{0008}\0a\U{000E}a\U{0002}a\U{0006}\U{000C}\naaaa\U{0004}aaaaaaaaaaaaa"| > |"\U{0008}\0a\U{000E}a\U{0002}a\U{0006}\U{000C}\naaaa\U{0004}aaaaaaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}\0a\U{000E}a\U{0002}a\U{0006}\U{000C}\naaaa\U{0004}aaaaaaaaaaaaa", "\U{0008}\0a\U{000E}a\U{0002}a\U{0006}\U{000C}\naaaa\U{0004}aaaaaaaaaaaaa");
}
method {:test} Test116() {
var r0 := isPrefix("\U{000E}aaaaaa\U{0006}a\U{0008}a\n\0", "\U{0010}\U{0004}\U{0002}aaaaaaaaa\U{000C}");
expect |"\U{000E}aaaaaa\U{0006}a\U{0008}a\n\0"| > |"\U{0010}\U{0004}\U{0002}aaaaaaaaa\U{000C}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000E}aaaaaa\U{0006}a\U{0008}a\n\0", "\U{0010}\U{0004}\U{0002}aaaaaaaaa\U{000C}");
}
method {:test} Test117() {
var r0 := isPrefix("\U{0008}aaaaaa\U{0004}a\U{0006}", "\0aaaaa\U{0002}");
expect |"\U{0008}aaaaaa\U{0004}a\U{0006}"| > |"\0aaaaa\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}aaaaaa\U{0004}a\U{0006}", "\0aaaaa\U{0002}");
}
method {:test} Test118() {
var r0 := isSubstring("\U{0004}aaa\U{0006}\U{0008}", "\n\0\U{0002}\U{0004}aaa\U{0006}\U{0008}");
expect r0 == isSubstringPredicate("\U{0004}aaa\U{0006}\U{0008}", "\n\0\U{0002}\U{0004}aaa\U{0006}\U{0008}");
}
method {:test} Test119() {
var r0 := isSubstring("\U{0008}aaaaa\U{0006}\0", "\U{000C}\U{0002}aa\U{0004}a\n");
expect r0 == isSubstringPredicate("\U{0008}aaaaa\U{0006}\0", "\U{000C}\U{0002}aa\U{0004}a\n");
}
method {:test} Test120() {
var r0 := haveCommonKSubstring(15, "\U{0002}a\0aaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}a\0aaaaaaaaaaaaaaaaaaa"| < 15 || |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 15 ==> !r0;
expect haveCommonKSubstringPredicate(15, "\U{0002}a\0aaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test121() {
var r0 := haveCommonKSubstring(15, "a\0aaaaaaa\U{0008}\n\U{000C}a\U{0010}a", "\U{0004}aaaaaa\U{0006}aaaaa\U{0012}\U{0014}\U{0002}\U{0016}a\U{000E}a\U{0018}");
expect |"a\0aaaaaaa\U{0008}\n\U{000C}a\U{0010}a"| < 15 || |"\U{0004}aaaaaa\U{0006}aaaaa\U{0012}\U{0014}\U{0002}\U{0016}a\U{000E}a\U{0018}"| < 15 ==> !r0;
expect haveCommonKSubstringPredicate(15, "a\0aaaaaaa\U{0008}\n\U{000C}a\U{0010}a", "\U{0004}aaaaaa\U{0006}aaaaa\U{0012}\U{0014}\U{0002}\U{0016}a\U{000E}a\U{0018}") == r0;
}
method {:test} Test122() {
var r0 := haveCommonKSubstring(103, "\U{000E}\U{0002}aaaaa\U{0004}a\U{0008}a\n", "\U{000C}aaaa\0a\U{0006}");
expect |"\U{000E}\U{0002}aaaaa\U{0004}a\U{0008}a\n"| < 103 || |"\U{000C}aaaa\0a\U{0006}"| < 103 ==> !r0;
expect haveCommonKSubstringPredicate(103, "\U{000E}\U{0002}aaaaa\U{0004}a\U{0008}a\n", "\U{000C}aaaa\0a\U{0006}") == r0;
}
method {:test} Test123() {
var r0 := maxCommonSubstringLength("\n\U{0002}\U{0004}", "\U{0006}\0aaaaaaaaaaaaaaa\U{0008}");
expect r0 <= |"\n\U{0002}\U{0004}"| && r0 <= |"\U{0006}\0aaaaaaaaaaaaaaa\U{0008}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\n\U{0002}\U{0004}", "\U{0006}\0aaaaaaaaaaaaaaa\U{0008}", r0);
}

// REPEAT 4 - TIME: 66.586957 s

method {:test} Test124() {
var r0 := isPrefix("\U{0004}\0a\U{0006}a\U{0002}", "\U{0004}\0a\U{0006}a\U{0002}");
expect |"\U{0004}\0a\U{0006}a\U{0002}"| > |"\U{0004}\0a\U{0006}a\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0a\U{0006}a\U{0002}", "\U{0004}\0a\U{0006}a\U{0002}");
}
method {:test} Test125() {
var r0 := isPrefix("\U{000E}a\U{0006}a\0aaaa", "\U{0010}\U{0004}a\n\U{0002}a\U{0008}\U{000C}a");
expect |"\U{000E}a\U{0006}a\0aaaa"| > |"\U{0010}\U{0004}a\n\U{0002}a\U{0008}\U{000C}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000E}a\U{0006}a\0aaaa", "\U{0010}\U{0004}a\n\U{0002}a\U{0008}\U{000C}a");
}
method {:test} Test126() {
var r0 := isPrefix("\naa\U{0002}aaaaa", "\U{000C}\0\U{0006}aaa\U{0004}\U{0008}");
expect |"\naa\U{0002}aaaaa"| > |"\U{000C}\0\U{0006}aaa\U{0004}\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\naa\U{0002}aaaaa", "\U{000C}\0\U{0006}aaa\U{0004}\U{0008}");
}
method {:test} Test127() {
var r0 := isSubstring("\U{0004}aa\U{0010}\U{0008}aaa\U{000C}", "\U{0012}\0a\U{0006}aaaaaa\U{000E}\n\U{0002}\U{0004}aa\U{0010}\U{0008}aaa\U{000C}aaaaaa");
expect r0 == isSubstringPredicate("\U{0004}aa\U{0010}\U{0008}aaa\U{000C}", "\U{0012}\0a\U{0006}aaaaaa\U{000E}\n\U{0002}\U{0004}aa\U{0010}\U{0008}aaa\U{000C}aaaaaa");
}
method {:test} Test128() {
var r0 := isSubstring("\n\U{0002}a\0aaaa\U{0008}aaaa", "\U{0006}\U{0004}");
expect r0 == isSubstringPredicate("\n\U{0002}a\0aaaa\U{0008}aaaa", "\U{0006}\U{0004}");
}
method {:test} Test129() {
var r0 := haveCommonKSubstring(16, "\U{001E}\0aaa\U{0004}aaa\U{0008}a\U{000C}\U{000E}\U{0010}aaaaa\U{0014}\U{001C}a\U{001A}aaaa\U{0018}\U{0016}a", "\U{0002}aaaaaa\U{0006}a\naaa\U{0012}aaaaa\U{0014}\U{001C}a\U{001A}aaaa\U{0018}\U{0016}a");
expect |"\U{001E}\0aaa\U{0004}aaa\U{0008}a\U{000C}\U{000E}\U{0010}aaaaa\U{0014}\U{001C}a\U{001A}aaaa\U{0018}\U{0016}a"| < 16 || |"\U{0002}aaaaaa\U{0006}a\naaa\U{0012}aaaaa\U{0014}\U{001C}a\U{001A}aaaa\U{0018}\U{0016}a"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "\U{001E}\0aaa\U{0004}aaa\U{0008}a\U{000C}\U{000E}\U{0010}aaaaa\U{0014}\U{001C}a\U{001A}aaaa\U{0018}\U{0016}a", "\U{0002}aaaaaa\U{0006}a\naaa\U{0012}aaaaa\U{0014}\U{001C}a\U{001A}aaaa\U{0018}\U{0016}a") == r0;
}
method {:test} Test130() {
var r0 := haveCommonKSubstring(16, "\U{001C}\0aaa\U{0004}aaa\U{0008}a\na\U{0010}\U{000E}\U{0014}", "\U{001E}aaaaaa\U{0006}aaa\U{000C}aaa\U{0016}\U{0002}\U{0018}aa\U{0012}\U{001A}");
expect |"\U{001C}\0aaa\U{0004}aaa\U{0008}a\na\U{0010}\U{000E}\U{0014}"| < 16 || |"\U{001E}aaaaaa\U{0006}aaa\U{000C}aaa\U{0016}\U{0002}\U{0018}aa\U{0012}\U{001A}"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "\U{001C}\0aaa\U{0004}aaa\U{0008}a\na\U{0010}\U{000E}\U{0014}", "\U{001E}aaaaaa\U{0006}aaa\U{000C}aaa\U{0016}\U{0002}\U{0018}aa\U{0012}\U{001A}") == r0;
}
method {:test} Test131() {
var r0 := haveCommonKSubstring(104, "\U{001E}\U{0002}aa\0aaaa\na\U{000C}a\U{000E}\U{0014}\U{0016}", "\U{0004}aaaaaa\U{0006}\U{0008}aaaa\U{0010}a\U{0018}aaa\U{0012}\U{001C}\U{001A}");
expect |"\U{001E}\U{0002}aa\0aaaa\na\U{000C}a\U{000E}\U{0014}\U{0016}"| < 104 || |"\U{0004}aaaaaa\U{0006}\U{0008}aaaa\U{0010}a\U{0018}aaa\U{0012}\U{001C}\U{001A}"| < 104 ==> !r0;
expect haveCommonKSubstringPredicate(104, "\U{001E}\U{0002}aa\0aaaa\na\U{000C}a\U{000E}\U{0014}\U{0016}", "\U{0004}aaaaaa\U{0006}\U{0008}aaaa\U{0010}a\U{0018}aaa\U{0012}\U{001C}\U{001A}") == r0;
}
method {:test} Test132() {
var r0 := maxCommonSubstringLength("aaa\U{0002}aaaaaa\U{0008}", "\n\0\U{0004}\U{0006}");
expect r0 <= |"aaa\U{0002}aaaaaa\U{0008}"| && r0 <= |"\n\0\U{0004}\U{0006}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaa\U{0002}aaaaaa\U{0008}", "\n\0\U{0004}\U{0006}", r0);
}

// REPEAT 5 - TIME: 72.4573662 s

method {:test} Test133() {
var r0 := isPrefix("\U{0004}\0aa\U{0002}", "\U{0004}\0aa\U{0002}aaa");
expect |"\U{0004}\0aa\U{0002}"| > |"\U{0004}\0aa\U{0002}aaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0aa\U{0002}", "\U{0004}\0aa\U{0002}aaa");
}
method {:test} Test134() {
var r0 := isPrefix("\U{0014}\U{0004}\0a", "\U{0012}a\U{0002}aaa\n\U{000E}a\U{0006}aaaaaaa\U{000C}aaaaa\U{0008}\U{0010}aaaa");
expect |"\U{0014}\U{0004}\0a"| > |"\U{0012}a\U{0002}aaa\n\U{000E}a\U{0006}aaaaaaa\U{000C}aaaaa\U{0008}\U{0010}aaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0014}\U{0004}\0a", "\U{0012}a\U{0002}aaa\n\U{000E}a\U{0006}aaaaaaa\U{000C}aaaaa\U{0008}\U{0010}aaaa");
}
method {:test} Test135() {
var r0 := isPrefix("\U{0018}aaaaaaaa\U{0012}aaaaaaaaaa\0a\U{000E}aaaa\U{0004}a", "\U{0016}\U{0002}\U{0006}aaaa\U{0008}aaa\U{0014}a\U{0010}aaaaaaaa\U{000C}aaa\n");
expect |"\U{0018}aaaaaaaa\U{0012}aaaaaaaaaa\0a\U{000E}aaaa\U{0004}a"| > |"\U{0016}\U{0002}\U{0006}aaaa\U{0008}aaa\U{0014}a\U{0010}aaaaaaaa\U{000C}aaa\n"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0018}aaaaaaaa\U{0012}aaaaaaaaaa\0a\U{000E}aaaa\U{0004}a", "\U{0016}\U{0002}\U{0006}aaaa\U{0008}aaa\U{0014}a\U{0010}aaaaaaaa\U{000C}aaa\n");
}
method {:test} Test136() {
var r0 := isSubstring("\U{0018}\U{0002}\0aa\U{000C}\U{0010}aa\U{0012}a\na\U{0014}", "\U{0016}aaa\U{0008}aa\U{000E}a\U{0004}\U{0006}aaaa\U{0018}\U{0002}\0aa\U{000C}\U{0010}aa\U{0012}a\na\U{0014}");
expect r0 == isSubstringPredicate("\U{0018}\U{0002}\0aa\U{000C}\U{0010}aa\U{0012}a\na\U{0014}", "\U{0016}aaa\U{0008}aa\U{000E}a\U{0004}\U{0006}aaaa\U{0018}\U{0002}\0aa\U{000C}\U{0010}aa\U{0012}a\na\U{0014}");
}
method {:test} Test137() {
var r0 := isSubstring("\n\U{0002}\U{0006}aa\0\U{000E}", "\U{0004}a\U{0008}\U{000C}");
expect r0 == isSubstringPredicate("\n\U{0002}\U{0006}aa\0\U{000E}", "\U{0004}a\U{0008}\U{000C}");
}
method {:test} Test138() {
var r0 := haveCommonKSubstring(17, "\U{0016}aaaaaaaaaa\U{0004}aaaa\U{0006}a\n\U{000C}aa\U{000E}aaaaa\U{0008}", "\U{0018}aaaa\0a\U{0002}aaaa\U{0006}a\n\U{000C}aa\U{000E}aaaaa\U{0008}a\U{0010}a\U{0014}\U{0012}");
expect |"\U{0016}aaaaaaaaaa\U{0004}aaaa\U{0006}a\n\U{000C}aa\U{000E}aaaaa\U{0008}"| < 17 || |"\U{0018}aaaa\0a\U{0002}aaaa\U{0006}a\n\U{000C}aa\U{000E}aaaaa\U{0008}a\U{0010}a\U{0014}\U{0012}"| < 17 ==> !r0;
expect haveCommonKSubstringPredicate(17, "\U{0016}aaaaaaaaaa\U{0004}aaaa\U{0006}a\n\U{000C}aa\U{000E}aaaaa\U{0008}", "\U{0018}aaaa\0a\U{0002}aaaa\U{0006}a\n\U{000C}aa\U{000E}aaaaa\U{0008}a\U{0010}a\U{0014}\U{0012}") == r0;
}
method {:test} Test139() {
var r0 := haveCommonKSubstring(17, " aaaaaaaaaa\U{0008}\U{0006}\n\U{0002}\U{000E}aa\U{0010}\U{000C}aa\U{0012}\U{001C}\U{001E}", "\"aaaaaa\U{0004}aa\0aaaaa\U{0014}a\U{0016}aa\U{0018}\U{001A}");
expect |" aaaaaaaaaa\U{0008}\U{0006}\n\U{0002}\U{000E}aa\U{0010}\U{000C}aa\U{0012}\U{001C}\U{001E}"| < 17 || |"\"aaaaaa\U{0004}aa\0aaaaa\U{0014}a\U{0016}aa\U{0018}\U{001A}"| < 17 ==> !r0;
expect haveCommonKSubstringPredicate(17, " aaaaaaaaaa\U{0008}\U{0006}\n\U{0002}\U{000E}aa\U{0010}\U{000C}aa\U{0012}\U{001C}\U{001E}", "\"aaaaaa\U{0004}aa\0aaaaa\U{0014}a\U{0016}aa\U{0018}\U{001A}") == r0;
}
method {:test} Test140() {
var r0 := haveCommonKSubstring(105, "\U{0002}aaaaaaaaa", "\0aaaaaaaaa");
expect |"\U{0002}aaaaaaaaa"| < 105 || |"\0aaaaaaaaa"| < 105 ==> !r0;
expect haveCommonKSubstringPredicate(105, "\U{0002}aaaaaaaaa", "\0aaaaaaaaa") == r0;
}
method {:test} Test141() {
var r0 := maxCommonSubstringLength("\naa\U{0002}aaaaaa\U{0004}\U{0006}", "\U{0008}\0aa");
expect r0 <= |"\naa\U{0002}aaaaaa\U{0004}\U{0006}"| && r0 <= |"\U{0008}\0aa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\naa\U{0002}aaaaaa\U{0004}\U{0006}", "\U{0008}\0aa", r0);
}

// REPEAT 6 - TIME: 79.5713412 s

method {:test} Test142() {
var r0 := isPrefix("\U{0016}\0\U{0004}aaaa\U{0002}\U{000E}\U{0010}a\U{0008}aaa", "\U{0016}\0\U{0004}aaaa\U{0002}\U{000E}\U{0010}a\U{0008}aaaaaaaa\U{0006}a\na\U{0014}\U{0012}a\U{000C}aa");
expect |"\U{0016}\0\U{0004}aaaa\U{0002}\U{000E}\U{0010}a\U{0008}aaa"| > |"\U{0016}\0\U{0004}aaaa\U{0002}\U{000E}\U{0010}a\U{0008}aaaaaaaa\U{0006}a\na\U{0014}\U{0012}a\U{000C}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0016}\0\U{0004}aaaa\U{0002}\U{000E}\U{0010}a\U{0008}aaa", "\U{0016}\0\U{0004}aaaa\U{0002}\U{000E}\U{0010}a\U{0008}aaaaaaaa\U{0006}a\na\U{0014}\U{0012}a\U{000C}aa");
}
method {:test} Test143() {
var r0 := isPrefix("\U{0018}a\0aa\U{0006}aaaaaaa\U{0010}\U{0008}a", "\U{0016}\U{0004}\U{0002}aaaa\na\U{000C}aaa\U{0012}\U{0014}\U{000E}");
expect |"\U{0018}a\0aa\U{0006}aaaaaaa\U{0010}\U{0008}a"| > |"\U{0016}\U{0004}\U{0002}aaaa\na\U{000C}aaa\U{0012}\U{0014}\U{000E}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0018}a\0aa\U{0006}aaaaaaa\U{0010}\U{0008}a", "\U{0016}\U{0004}\U{0002}aaaa\na\U{000C}aaa\U{0012}\U{0014}\U{000E}");
}
method {:test} Test144() {
var r0 := isPrefix("\U{0014}aaaa\U{0002}aaaaaaaa\U{0004}aa\U{000E}aaaaaaa\U{0008}aa", "\U{0012}\0aaaaa\U{0006}a\na\U{000C}a\U{0010}");
expect |"\U{0014}aaaa\U{0002}aaaaaaaa\U{0004}aa\U{000E}aaaaaaa\U{0008}aa"| > |"\U{0012}\0aaaaa\U{0006}a\na\U{000C}a\U{0010}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0014}aaaa\U{0002}aaaaaaaa\U{0004}aa\U{000E}aaaaaaa\U{0008}aa", "\U{0012}\0aaaaa\U{0006}a\na\U{000C}a\U{0010}");
}
method {:test} Test145() {
var r0 := isSubstring("a\U{0002}aaa\U{0010}\U{0012}\U{000E}a\U{0014}\U{000C}\0\U{0016}\U{0018}\U{001A}", "\U{001E}aaaa\U{0008}aa\U{0004}aaa\U{0006}\na\U{0002}aaa\U{0010}\U{0012}\U{000E}a\U{0014}\U{000C}\0\U{0016}\U{0018}\U{001A}\U{001C}");
expect r0 == isSubstringPredicate("a\U{0002}aaa\U{0010}\U{0012}\U{000E}a\U{0014}\U{000C}\0\U{0016}\U{0018}\U{001A}", "\U{001E}aaaa\U{0008}aa\U{0004}aaa\U{0006}\na\U{0002}aaa\U{0010}\U{0012}\U{000E}a\U{0014}\U{000C}\0\U{0016}\U{0018}\U{001A}\U{001C}");
}
method {:test} Test146() {
var r0 := isSubstring("\U{000C}\U{0002}aaa\U{0008}a\0", "\naa\U{0004}\U{0006}");
expect r0 == isSubstringPredicate("\U{000C}\U{0002}aaa\U{0008}a\0", "\naa\U{0004}\U{0006}");
}
method {:test} Test147() {
var r0 := haveCommonKSubstring(18, "\U{000E}aaaaaaaaa\U{0004}aaaaaaaaaa\U{0008}aa\U{000C}aa\na\U{0006}", "aaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0008}aa\U{000C}aa\na");
expect |"\U{000E}aaaaaaaaa\U{0004}aaaaaaaaaa\U{0008}aa\U{000C}aa\na\U{0006}"| < 18 || |"aaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0008}aa\U{000C}aa\na"| < 18 ==> !r0;
expect haveCommonKSubstringPredicate(18, "\U{000E}aaaaaaaaa\U{0004}aaaaaaaaaa\U{0008}aa\U{000C}aa\na\U{0006}", "aaaaaaaaa\0\U{0002}aaaaaaaaaa\U{0008}aa\U{000C}aa\na") == r0;
}
method {:test} Test148() {
var r0 := haveCommonKSubstring(18, "a\0aaaaaaa\U{0008}a\U{000C}aaaaaaaa\U{0010}\U{0012}aaaaaa", "\U{0004}a\U{0002}aaaa\U{0006}aaaaa\U{000E}aaaaaaa\na\U{0014}");
expect |"a\0aaaaaaa\U{0008}a\U{000C}aaaaaaaa\U{0010}\U{0012}aaaaaa"| < 18 || |"\U{0004}a\U{0002}aaaa\U{0006}aaaaa\U{000E}aaaaaaa\na\U{0014}"| < 18 ==> !r0;
expect haveCommonKSubstringPredicate(18, "a\0aaaaaaa\U{0008}a\U{000C}aaaaaaaa\U{0010}\U{0012}aaaaaa", "\U{0004}a\U{0002}aaaa\U{0006}aaaaa\U{000E}aaaaaaa\na\U{0014}") == r0;
}
method {:test} Test149() {
var r0 := haveCommonKSubstring(106, "\U{000E}aaaaaaaaaaaaaaaaa\0\U{0006}\U{0004}aa", "aaaaaaaaaaa\U{0002}aaaaaaaaa\n\U{0008}\U{000C}");
expect |"\U{000E}aaaaaaaaaaaaaaaaa\0\U{0006}\U{0004}aa"| < 106 || |"aaaaaaaaaaa\U{0002}aaaaaaaaa\n\U{0008}\U{000C}"| < 106 ==> !r0;
expect haveCommonKSubstringPredicate(106, "\U{000E}aaaaaaaaaaaaaaaaa\0\U{0006}\U{0004}aa", "aaaaaaaaaaa\U{0002}aaaaaaaaa\n\U{0008}\U{000C}") == r0;
}
method {:test} Test150() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaa\U{0006}\U{0008}", "\U{0004}\0aa\U{0002}");
expect r0 <= |"aaaaaaaaaaa\U{0006}\U{0008}"| && r0 <= |"\U{0004}\0aa\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaa\U{0006}\U{0008}", "\U{0004}\0aa\U{0002}", r0);
}

// REPEAT 7 - TIME: 86.0663028 s

method {:test} Test151() {
var r0 := isPrefix("\U{0010}aaaa\U{0002}aa\U{0008}aa\0a\U{0006}", "\U{0010}aaaa\U{0002}aa\U{0008}aa\0a\U{0006}\U{0012}a\naa\U{000C}a\U{000E}aaaaa\U{0004}aa");
expect |"\U{0010}aaaa\U{0002}aa\U{0008}aa\0a\U{0006}"| > |"\U{0010}aaaa\U{0002}aa\U{0008}aa\0a\U{0006}\U{0012}a\naa\U{000C}a\U{000E}aaaaa\U{0004}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0010}aaaa\U{0002}aa\U{0008}aa\0a\U{0006}", "\U{0010}aaaa\U{0002}aa\U{0008}aa\0a\U{0006}\U{0012}a\naa\U{000C}a\U{000E}aaaaa\U{0004}aa");
}
method {:test} Test152() {
var r0 := isPrefix("\U{000C}\U{0004}aaaaa\0\U{0006}aa\naaa", "\U{0008}aaaaaa\U{0002}aaaaaaa");
expect |"\U{000C}\U{0004}aaaaa\0\U{0006}aa\naaa"| > |"\U{0008}aaaaaa\U{0002}aaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}\U{0004}aaaaa\0\U{0006}aa\naaa", "\U{0008}aaaaaa\U{0002}aaaaaaa");
}
method {:test} Test153() {
var r0 := isPrefix("aaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}aaaa", "\U{000E}\0aaaaa\U{0004}aa\U{0008}aa\n\U{000C}aa");
expect |"aaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}aaaa"| > |"\U{000E}\0aaaaa\U{0004}aa\U{0008}aa\n\U{000C}aa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}aaaa", "\U{000E}\0aaaaa\U{0004}aa\U{0008}aa\n\U{000C}aa");
}
method {:test} Test154() {
var r0 := isSubstring("\U{0018}aa\0a\U{000C}aa\U{0006}\U{0010}a\U{0012}\U{0016}", "\U{001A}\U{0002}a\na\U{0008}\U{000E}\U{0004}a\U{0014}a\U{0018}aa\0a\U{000C}aa\U{0006}\U{0010}a\U{0012}\U{0016}aa");
expect r0 == isSubstringPredicate("\U{0018}aa\0a\U{000C}aa\U{0006}\U{0010}a\U{0012}\U{0016}", "\U{001A}\U{0002}a\na\U{0008}\U{000E}\U{0004}a\U{0014}a\U{0018}aa\0a\U{000C}aa\U{0006}\U{0010}a\U{0012}\U{0016}aa");
}
method {:test} Test155() {
var r0 := isSubstring("\U{0010}\U{0004}\U{000C}aaaa\U{000E}aaa\0", "\n\U{0002}aa\U{0006}\U{0008}");
expect r0 == isSubstringPredicate("\U{0010}\U{0004}\U{000C}aaaa\U{000E}aaa\0", "\n\U{0002}aa\U{0006}\U{0008}");
}
method {:test} Test156() {
var r0 := haveCommonKSubstring(19, "aaa\0aaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}\U{0008}", "aaaaaaaaaaaaaaaaaaaa\naa\U{000E}a\U{000C}\U{0002}a");
expect |"aaa\0aaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}\U{0008}"| < 19 || |"aaaaaaaaaaaaaaaaaaaa\naa\U{000E}a\U{000C}\U{0002}a"| < 19 ==> !r0;
expect haveCommonKSubstringPredicate(19, "aaa\0aaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}\U{0008}", "aaaaaaaaaaaaaaaaaaaa\naa\U{000E}a\U{000C}\U{0002}a") == r0;
}
method {:test} Test157() {
var r0 := haveCommonKSubstring(19, "aaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa\na\U{0010}a", "\U{0012}aaaaaa\0aaaaa\U{0006}a\U{0008}aaaaaaaaaaa\U{000C}\U{000E}");
expect |"aaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa\na\U{0010}a"| < 19 || |"\U{0012}aaaaaa\0aaaaa\U{0006}a\U{0008}aaaaaaaaaaa\U{000C}\U{000E}"| < 19 ==> !r0;
expect haveCommonKSubstringPredicate(19, "aaaaaaaaaaa\U{0002}aa\U{0004}aaaaaaaa\na\U{0010}a", "\U{0012}aaaaaa\0aaaaa\U{0006}a\U{0008}aaaaaaaaaaa\U{000C}\U{000E}") == r0;
}
method {:test} Test158() {
var r0 := haveCommonKSubstring(107, "aaaaaaaaaaaaaaa\U{0006}a\U{0004}aaaaaa\0\U{0012}a", "aaaaaaaaaaaaaa\U{0002}aaa\U{0008}a\n\U{000C}\U{000E}a\U{0010}");
expect |"aaaaaaaaaaaaaaa\U{0006}a\U{0004}aaaaaa\0\U{0012}a"| < 107 || |"aaaaaaaaaaaaaa\U{0002}aaa\U{0008}a\n\U{000C}\U{000E}a\U{0010}"| < 107 ==> !r0;
expect haveCommonKSubstringPredicate(107, "aaaaaaaaaaaaaaa\U{0006}a\U{0004}aaaaaa\0\U{0012}a", "aaaaaaaaaaaaaa\U{0002}aaa\U{0008}a\n\U{000C}\U{000E}a\U{0010}") == r0;
}
method {:test} Test159() {
var r0 := maxCommonSubstringLength("\U{0004}\0aa", "\U{0002}aaaaaaaaaaaaaaaaa");
expect r0 <= |"\U{0004}\0aa"| && r0 <= |"\U{0002}aaaaaaaaaaaaaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}\0aa", "\U{0002}aaaaaaaaaaaaaaaaa", r0);
}

// REPEAT 8 - TIME: 93.2061515 s

method {:test} Test160() {
var r0 := isPrefix("a\0aaaaaaaaa\U{0004}a\U{0008}aaaaaaaa\U{0006}a", "a\0aaaaaaaaa\U{0004}a\U{0008}aaaaaaaa\U{0006}aa\U{0002}");
expect |"a\0aaaaaaaaa\U{0004}a\U{0008}aaaaaaaa\U{0006}a"| > |"a\0aaaaaaaaa\U{0004}a\U{0008}aaaaaaaa\U{0006}aa\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaaaaaaaa\U{0004}a\U{0008}aaaaaaaa\U{0006}a", "a\0aaaaaaaaa\U{0004}a\U{0008}aaaaaaaa\U{0006}aa\U{0002}");
}
method {:test} Test161() {
var r0 := isPrefix("\U{001E}aaaaa\U{0006}aa\U{0012}aa\U{0014}aa\U{000E}aaaa\U{0008}\0aa\U{001A}a", " \U{0004}aaaaa\na\U{0010}a\U{0018}aa\U{000C}a\U{0016}aaaa\U{0002}aa\U{001C}aa");
expect |"\U{001E}aaaaa\U{0006}aa\U{0012}aa\U{0014}aa\U{000E}aaaa\U{0008}\0aa\U{001A}a"| > |" \U{0004}aaaaa\na\U{0010}a\U{0018}aa\U{000C}a\U{0016}aaaa\U{0002}aa\U{001C}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{001E}aaaaa\U{0006}aa\U{0012}aa\U{0014}aa\U{000E}aaaa\U{0008}\0aa\U{001A}a", " \U{0004}aaaaa\na\U{0010}a\U{0018}aa\U{000C}a\U{0016}aaaa\U{0002}aa\U{001C}aa");
}
method {:test} Test162() {
var r0 := isPrefix("\U{000C}aaaaaaaaaaaa\0aaaaa\U{0004}aaaaaaa", "\naaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaa\U{0002}a");
expect |"\U{000C}aaaaaaaaaaaa\0aaaaa\U{0004}aaaaaaa"| > |"\naaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaa\U{0002}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}aaaaaaaaaaaa\0aaaaa\U{0004}aaaaaaa", "\naaaaaaaaaaaa\U{0006}a\U{0008}aaaaaaaa\U{0002}a");
}
method {:test} Test163() {
var r0 := isSubstring("aaaaaa\0\U{000C}\n\U{0010}a\U{0012}\U{0014}\U{0016}\U{0018}\U{001A}", "\U{001E}aaaa\U{0008}aa\U{0004}\U{0006}\U{000E}\U{0002}aaaaaa\0\U{000C}\n\U{0010}a\U{0012}\U{0014}\U{0016}\U{0018}\U{001A}a\U{001C}");
expect r0 == isSubstringPredicate("aaaaaa\0\U{000C}\n\U{0010}a\U{0012}\U{0014}\U{0016}\U{0018}\U{001A}", "\U{001E}aaaa\U{0008}aa\U{0004}\U{0006}\U{000E}\U{0002}aaaaaa\0\U{000C}\n\U{0010}a\U{0012}\U{0014}\U{0016}\U{0018}\U{001A}a\U{001C}");
}
method {:test} Test164() {
var r0 := isSubstring("aaaaaaa\na\U{000C}aaa\U{0010}\U{000E}\U{0012}", "\U{0014}aaaa\U{0002}a\0a\U{0004}a\U{0008}\U{0006}a");
expect r0 == isSubstringPredicate("aaaaaaa\na\U{000C}aaa\U{0010}\U{000E}\U{0012}", "\U{0014}aaaa\U{0002}a\0a\U{0004}a\U{0008}\U{0006}a");
}
method {:test} Test165() {
var r0 := haveCommonKSubstring(20, "\U{0008}aaaaaaaaaaaaaa\0\U{0002}aaa\U{0004}", "aaaaaaaaaaaaaaaaaaaa\0\U{0002}aaa\U{0004}\U{0006}");
expect |"\U{0008}aaaaaaaaaaaaaa\0\U{0002}aaa\U{0004}"| < 20 || |"aaaaaaaaaaaaaaaaaaaa\0\U{0002}aaa\U{0004}\U{0006}"| < 20 ==> !r0;
expect haveCommonKSubstringPredicate(20, "\U{0008}aaaaaaaaaaaaaa\0\U{0002}aaa\U{0004}", "aaaaaaaaaaaaaaaaaaaa\0\U{0002}aaa\U{0004}\U{0006}") == r0;
}
method {:test} Test166() {
var r0 := haveCommonKSubstring(21, "a\0aaaaaaaaa\na\U{000E}aaaaaaaaaaaa", "\U{0004}aa\U{0002}aaa\U{0006}a\U{0008}aaaaaaaaaaa\U{000C}aaaa");
expect |"a\0aaaaaaaaa\na\U{000E}aaaaaaaaaaaa"| < 21 || |"\U{0004}aa\U{0002}aaa\U{0006}a\U{0008}aaaaaaaaaaa\U{000C}aaaa"| < 21 ==> !r0;
expect haveCommonKSubstringPredicate(21, "a\0aaaaaaaaa\na\U{000E}aaaaaaaaaaaa", "\U{0004}aa\U{0002}aaa\U{0006}a\U{0008}aaaaaaaaaaa\U{000C}aaaa") == r0;
}
method {:test} Test167() {
var r0 := haveCommonKSubstring(108, "\U{000C}\U{0002}aaaaaaa\U{0008}a\naaa\U{0006}aaaaaaaaa\0", "\U{0004}a");
expect |"\U{000C}\U{0002}aaaaaaa\U{0008}a\naaa\U{0006}aaaaaaaaa\0"| < 108 || |"\U{0004}a"| < 108 ==> !r0;
expect haveCommonKSubstringPredicate(108, "\U{000C}\U{0002}aaaaaaa\U{0008}a\naaa\U{0006}aaaaaaaaa\0", "\U{0004}a") == r0;
}
method {:test} Test168() {
var r0 := maxCommonSubstringLength("\naaa\U{0006}", "\U{000C}\0a\U{0002}\U{0008}\U{0004}");
expect r0 <= |"\naaa\U{0006}"| && r0 <= |"\U{000C}\0a\U{0002}\U{0008}\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\naaa\U{0006}", "\U{000C}\0a\U{0002}\U{0008}\U{0004}", r0);
}

// REPEAT 9 - TIME: 99.6095338 s

method {:test} Test169() {
var r0 := isPrefix("a\0aaaaaaaaa\U{0006}a\naaa\U{0008}aaaaa", "a\0aaaaaaaaa\U{0006}a\naaa\U{0008}aaaaa\U{0004}\U{0002}");
expect |"a\0aaaaaaaaa\U{0006}a\naaa\U{0008}aaaaa"| > |"a\0aaaaaaaaa\U{0006}a\naaa\U{0008}aaaaa\U{0004}\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaaaaaaaa\U{0006}a\naaa\U{0008}aaaaa", "a\0aaaaaaaaa\U{0006}a\naaa\U{0008}aaaaa\U{0004}\U{0002}");
}
method {:test} Test170() {
var r0 := isPrefix("\U{0016}aaaaaaaaaaaa\U{000E}aaa\U{0004}aaaaa\0aaaa\U{0012}", "\U{0014}aaaaaa\U{0006}a\na\U{000C}aaaaaaaa\U{0008}aa\U{0002}aaa\U{0010}a");
expect |"\U{0016}aaaaaaaaaaaa\U{000E}aaa\U{0004}aaaaa\0aaaa\U{0012}"| > |"\U{0014}aaaaaa\U{0006}a\na\U{000C}aaaaaaaa\U{0008}aa\U{0002}aaa\U{0010}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0016}aaaaaaaaaaaa\U{000E}aaa\U{0004}aaaaa\0aaaa\U{0012}", "\U{0014}aaaaaa\U{0006}a\na\U{000C}aaaaaaaa\U{0008}aa\U{0002}aaa\U{0010}a");
}
method {:test} Test171() {
var r0 := isPrefix("aaaaaaaaaaaaaaaaaaaaaaa\naaa\0a\U{000E}", "\U{0010}aaaaaa\U{0002}a\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}aa\U{000C}a");
expect |"aaaaaaaaaaaaaaaaaaaaaaa\naaa\0a\U{000E}"| > |"\U{0010}aaaaaa\U{0002}a\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}aa\U{000C}a"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaaaaaaaaaaaaaaaa\naaa\0a\U{000E}", "\U{0010}aaaaaa\U{0002}a\U{0008}aaaaa\U{0004}aaaaaaaa\U{0006}aa\U{000C}a");
}
method {:test} Test172() {
var r0 := isSubstring("\U{001A}aaaaa\U{000C}\U{0008}\U{000E}\U{0010}a\U{0006}\U{0014}a\U{0016}", "\U{001C}aaa\0\U{0004}aaaa\U{0002}a\n\U{0012}\U{0018}\U{001A}aaaaa\U{000C}\U{0008}\U{000E}\U{0010}a\U{0006}\U{0014}a\U{0016}");
expect r0 == isSubstringPredicate("\U{001A}aaaaa\U{000C}\U{0008}\U{000E}\U{0010}a\U{0006}\U{0014}a\U{0016}", "\U{001C}aaa\0\U{0004}aaaa\U{0002}a\n\U{0012}\U{0018}\U{001A}aaaaa\U{000C}\U{0008}\U{000E}\U{0010}a\U{0006}\U{0014}a\U{0016}");
}
method {:test} Test173() {
var r0 := isSubstring("aaaaaaa\U{0006}a\U{000E}a\U{0010}a\U{0008}a\U{0018}a\U{001A}a\U{0012}a\U{001C}aaa\na\U{0014}aa", " aa\U{0002}a\U{0004}aaaaaaaaaaaaaaa\U{000C}aa\0aa\U{0016}\U{001E}");
expect r0 == isSubstringPredicate("aaaaaaa\U{0006}a\U{000E}a\U{0010}a\U{0008}a\U{0018}a\U{001A}a\U{0012}a\U{001C}aaa\na\U{0014}aa", " aa\U{0002}a\U{0004}aaaaaaaaaaaaaaa\U{000C}aa\0aa\U{0016}\U{001E}");
}
method {:test} Test174() {
var r0 := haveCommonKSubstring(22, "\U{0008}a\U{000C}aaaaaaaaaaaaaaaa\U{0002}a\U{0006}", "\na\0a\U{0008}a\U{000C}aaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}");
expect |"\U{0008}a\U{000C}aaaaaaaaaaaaaaaa\U{0002}a\U{0006}"| < 22 || |"\na\0a\U{0008}a\U{000C}aaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}"| < 22 ==> !r0;
expect haveCommonKSubstringPredicate(22, "\U{0008}a\U{000C}aaaaaaaaaaaaaaaa\U{0002}a\U{0006}", "\na\0a\U{0008}a\U{000C}aaaaaaaaaaaaaaaa\U{0002}a\U{0006}\U{0004}") == r0;
}
method {:test} Test175() {
var r0 := haveCommonKSubstring(28, "\U{0010}aaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0008}\n", "\U{000E}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\U{0004}a\U{000C}");
expect |"\U{0010}aaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0008}\n"| < 28 || |"\U{000E}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\U{0004}a\U{000C}"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "\U{0010}aaaaaaaaaaaaaaaaaaaaaa\0aaa\U{0008}\n", "\U{000E}aaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\U{0004}a\U{000C}") == r0;
}
method {:test} Test176() {
var r0 := haveCommonKSubstring(109, "\naaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}");
expect |"\naaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}"| < 109 || |"\U{0008}aaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}"| < 109 ==> !r0;
expect haveCommonKSubstringPredicate(109, "\naaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}") == r0;
}
method {:test} Test177() {
var r0 := maxCommonSubstringLength("aaaaa\U{000C}aaa\U{0006}a\U{000E}a\U{0012}aa\U{0004}\U{0002}aa\U{0010}a\U{001A}", "a\0aa\U{0008}aaa\naaaaaaaa\U{0014}\U{0018}aaaaaaaaa\U{0016}");
expect r0 <= |"aaaaa\U{000C}aaa\U{0006}a\U{000E}a\U{0012}aa\U{0004}\U{0002}aa\U{0010}a\U{001A}"| && r0 <= |"a\0aa\U{0008}aaa\naaaaaaaa\U{0014}\U{0018}aaaaaaaaa\U{0016}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaa\U{000C}aaa\U{0006}a\U{000E}a\U{0012}aa\U{0004}\U{0002}aa\U{0010}a\U{001A}", "a\0aa\U{0008}aaa\naaaaaaaa\U{0014}\U{0018}aaaaaaaaa\U{0016}", r0);
}

// REPEAT 10 - TIME: 107.6008562 s

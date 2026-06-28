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
  return false;
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

// REPEAT 1 - TIME: 76.9532993 s

method {:test} Test97() {
var r0 := isPrefix("\U{000C}\0aaaa\U{0006}\n", "\U{000C}\0aaaa\U{0006}\na\U{0002}\U{0008}\U{0004}");
expect |"\U{000C}\0aaaa\U{0006}\n"| > |"\U{000C}\0aaaa\U{0006}\na\U{0002}\U{0008}\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}\0aaaa\U{0006}\n", "\U{000C}\0aaaa\U{0006}\na\U{0002}\U{0008}\U{0004}");
}
method {:test} Test98() {
var r0 := isPrefix("\U{0008}a\U{0002}", "\U{0006}\0a\U{0004}");
expect |"\U{0008}a\U{0002}"| > |"\U{0006}\0a\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}a\U{0002}", "\U{0006}\0a\U{0004}");
}
method {:test} Test99() {
var r0 := isPrefix("\U{0008}a\0a", "\U{0006}\U{0002}\U{0004}");
expect |"\U{0008}a\0a"| > |"\U{0006}\U{0002}\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}a\0a", "\U{0006}\U{0002}\U{0004}");
}
method {:test} Test100() {
var r0 := isSubstring("\U{0006}aaa\U{0004}a", "\U{0002}\0aa\U{0006}aaa\U{0004}a");
expect r0 == isSubstringPredicate("\U{0006}aaa\U{0004}a", "\U{0002}\0aa\U{0006}aaa\U{0004}a");
}
method {:test} Test101() {
var r0 := isSubstring("\U{0008}a\0a\U{0004}", "\U{0006}aa\U{0002}");
expect r0 == isSubstringPredicate("\U{0008}a\0a\U{0004}", "\U{0006}aa\U{0002}");
}
method {:test} Test102() {
var r0 := haveCommonKSubstring(13, "\0aaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaa"| < 13 || |"\U{0002}aaaaaaaaaaaaaaaaaaa"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "\0aaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test103() {
var r0 := haveCommonKSubstring(13, "a\0aaaaaa\U{0006}aa\U{0008}a", "\U{0004}a\U{0002}aaaaaaaaa\n");
expect |"a\0aaaaaa\U{0006}aa\U{0008}a"| < 13 || |"\U{0004}a\U{0002}aaaaaaaaa\n"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "a\0aaaaaa\U{0006}aa\U{0008}a", "\U{0004}a\U{0002}aaaaaaaaa\n") == r0;
}
method {:test} Test104() {
var r0 := haveCommonKSubstring(101, "\U{000C}\U{0004}\U{0002}", "\na\U{0006}aaaa\U{0008}a\0");
expect |"\U{000C}\U{0004}\U{0002}"| < 101 || |"\na\U{0006}aaaa\U{0008}a\0"| < 101 ==> !r0;
expect haveCommonKSubstringPredicate(101, "\U{000C}\U{0004}\U{0002}", "\na\U{0006}aaaa\U{0008}a\0") == r0;
}
method {:test} Test105() {
var r0 := maxCommonSubstringLength("a\0a", "aaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <= |"a\0a"| && r0 <= |"aaaaaaaaaaaaaaaaaaaaa\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0a", "aaaaaaaaaaaaaaaaaaaaa\U{0002}", r0);
}

// REPEAT 2 - TIME: 82.8451116 s

method {:test} Test106() {
var r0 := isPrefix("\U{0008}\0aa\U{0002}", "\U{0008}\0aa\U{0002}\U{0006}aaaa\U{0004}a");
expect |"\U{0008}\0aa\U{0002}"| > |"\U{0008}\0aa\U{0002}\U{0006}aaaa\U{0004}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}\0aa\U{0002}", "\U{0008}\0aa\U{0002}\U{0006}aaaa\U{0004}a");
}
method {:test} Test107() {
var r0 := isPrefix("\n\U{0002}a\U{0004}\U{0008}", "\U{000C}\0a\U{0006}a");
expect |"\n\U{0002}a\U{0004}\U{0008}"| > |"\U{000C}\0a\U{0006}a"| ==> !r0;
expect r0 == isPrefixPredicate("\n\U{0002}a\U{0004}\U{0008}", "\U{000C}\0a\U{0006}a");
}
method {:test} Test108() {
var r0 := isPrefix("\U{0008}aa\U{0004}\U{0006}", "\U{0002}\0");
expect |"\U{0008}aa\U{0004}\U{0006}"| > |"\U{0002}\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}aa\U{0004}\U{0006}", "\U{0002}\0");
}
method {:test} Test109() {
var r0 := isSubstring("\U{0008}a\0a", "\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\0a");
expect r0 == isSubstringPredicate("\U{0008}a\0a", "\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0002}\U{0008}a\0a");
}
method {:test} Test110() {
var r0 := isSubstring("\U{000E}aa\U{0004}\n\U{0008}aaaaaaaaaa", "\U{0010}\U{0002}a\U{0006}aaaaaaaa\0a\U{000C}");
expect r0 == isSubstringPredicate("\U{000E}aa\U{0004}\n\U{0008}aaaaaaaaaa", "\U{0010}\U{0002}a\U{0006}aaaaaaaa\0a\U{000C}");
}
method {:test} Test111() {
var r0 := haveCommonKSubstring(14, "\U{0004}\0aaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa");
expect |"\U{0004}\0aaaaaaaaaaaaaaaaaaa"| < 14 || |"\U{0006}aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa"| < 14 ==> !r0;
expect haveCommonKSubstringPredicate(14, "\U{0004}\0aaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test112() {
var r0 := haveCommonKSubstring(14, "\U{000E}\0aaaaaaa\U{0004}a\na\U{000C}", "aaaaaaa\U{0002}aaa\U{0006}a\U{0008}");
expect |"\U{000E}\0aaaaaaa\U{0004}a\na\U{000C}"| < 14 || |"aaaaaaa\U{0002}aaa\U{0006}a\U{0008}"| < 14 ==> !r0;
expect haveCommonKSubstringPredicate(14, "\U{000E}\0aaaaaaa\U{0004}a\na\U{000C}", "aaaaaaa\U{0002}aaa\U{0006}a\U{0008}") == r0;
}
method {:test} Test113() {
var r0 := haveCommonKSubstring(102, "\U{0016}\U{0004}aaa\0aaa\na\U{000E}aaaaaaa\U{0012}", "\U{0018}aa\U{0006}a\U{0002}a\U{0008}a\U{000C}aa\U{0010}\U{0014}");
expect |"\U{0016}\U{0004}aaa\0aaa\na\U{000E}aaaaaaa\U{0012}"| < 102 || |"\U{0018}aa\U{0006}a\U{0002}a\U{0008}a\U{000C}aa\U{0010}\U{0014}"| < 102 ==> !r0;
expect haveCommonKSubstringPredicate(102, "\U{0016}\U{0004}aaa\0aaa\na\U{000E}aaaaaaa\U{0012}", "\U{0018}aa\U{0006}a\U{0002}a\U{0008}a\U{000C}aa\U{0010}\U{0014}") == r0;
}
method {:test} Test114() {
var r0 := maxCommonSubstringLength("\U{0006}\0aaaaaaaaaaaaaaaaaaa\U{0002}", "aaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0008}");
expect r0 <= |"\U{0006}\0aaaaaaaaaaaaaaaaaaa\U{0002}"| && r0 <= |"aaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0008}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}\0aaaaaaaaaaaaaaaaaaa\U{0002}", "aaaaaaaaa\U{0004}aaaaaaaaaaaa\U{0008}", r0);
}

// REPEAT 3 - TIME: 90.3310282 s

method {:test} Test115() {
var r0 := isPrefix("\U{0006}\0aaa\U{0002}a", "\U{0006}\0aaa\U{0002}a\U{0004}");
expect |"\U{0006}\0aaa\U{0002}a"| > |"\U{0006}\0aaa\U{0002}a\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\0aaa\U{0002}a", "\U{0006}\0aaa\U{0002}a\U{0004}");
}
method {:test} Test116() {
var r0 := isPrefix("\U{0014}\U{0004}\0\U{0006}\U{000C}a", "\U{0016}\U{0002}\U{0008}a\n\U{0010}a\U{0012}a\U{000E}");
expect |"\U{0014}\U{0004}\0\U{0006}\U{000C}a"| > |"\U{0016}\U{0002}\U{0008}a\n\U{0010}a\U{0012}a\U{000E}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0014}\U{0004}\0\U{0006}\U{000C}a", "\U{0016}\U{0002}\U{0008}a\n\U{0010}a\U{0012}a\U{000E}");
}
method {:test} Test117() {
var r0 := isPrefix("\U{0012}\0aaa\na\U{0002}a\U{0008}a\U{0010}\U{000E}aa", "\U{0004}aaa\U{0006}a\U{000C}");
expect |"\U{0012}\0aaa\na\U{0002}a\U{0008}a\U{0010}\U{000E}aa"| > |"\U{0004}aaa\U{0006}a\U{000C}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0012}\0aaa\na\U{0002}a\U{0008}a\U{0010}\U{000E}aa", "\U{0004}aaa\U{0006}a\U{000C}");
}
method {:test} Test118() {
var r0 := isSubstring("a\0\U{0010}\U{0002}aaa\U{0008}aaa\U{0004}\U{000C}", "\U{000E}aaaaaaaaaa\naaa\U{0006}a\0\U{0010}\U{0002}aaa\U{0008}aaa\U{0004}\U{000C}a");
expect r0 == isSubstringPredicate("a\0\U{0010}\U{0002}aaa\U{0008}aaa\U{0004}\U{000C}", "\U{000E}aaaaaaaaaa\naaa\U{0006}a\0\U{0010}\U{0002}aaa\U{0008}aaa\U{0004}\U{000C}a");
}
method {:test} Test119() {
var r0 := isSubstring("\U{0010}aaa\U{0008}\U{0004}aaa\U{000C}a", "\U{000E}\U{0002}aaaa\n\U{0006}a\0");
expect r0 == isSubstringPredicate("\U{0010}aaa\U{0008}\U{0004}aaa\U{000C}a", "\U{000E}\U{0002}aaaa\n\U{0006}a\0");
}
method {:test} Test120() {
var r0 := haveCommonKSubstring(15, "\U{0008}\U{0002}aa\U{0004}aaaaaaaaaaaaaaa", "\na\0aaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaa");
expect |"\U{0008}\U{0002}aa\U{0004}aaaaaaaaaaaaaaa"| < 15 || |"\na\0aaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaa"| < 15 ==> !r0;
expect haveCommonKSubstringPredicate(15, "\U{0008}\U{0002}aa\U{0004}aaaaaaaaaaaaaaa", "\na\0aaaaaaa\U{0006}aaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test121() {
var r0 := haveCommonKSubstring(15, "aaa\U{0004}aaaaa\U{0008}a\U{000C}aaaaaaa\U{0010}a\U{0012}", "\U{0002}\0aaaaa\U{0006}aaaaaaaaaaaaa\U{000E}aa\naa\U{0014}");
expect |"aaa\U{0004}aaaaa\U{0008}a\U{000C}aaaaaaa\U{0010}a\U{0012}"| < 15 || |"\U{0002}\0aaaaa\U{0006}aaaaaaaaaaaaa\U{000E}aa\naa\U{0014}"| < 15 ==> !r0;
expect haveCommonKSubstringPredicate(15, "aaa\U{0004}aaaaa\U{0008}a\U{000C}aaaaaaa\U{0010}a\U{0012}", "\U{0002}\0aaaaa\U{0006}aaaaaaaaaaaaa\U{000E}aa\naa\U{0014}") == r0;
}
method {:test} Test122() {
var r0 := haveCommonKSubstring(103, "\U{0010}aaaaaaa\U{0006}\U{000C}a\U{000E}a\0a", "\U{0004}\U{0002}aaaaa\U{0008}aaa\n");
expect |"\U{0010}aaaaaaa\U{0006}\U{000C}a\U{000E}a\0a"| < 103 || |"\U{0004}\U{0002}aaaaa\U{0008}aaa\n"| < 103 ==> !r0;
expect haveCommonKSubstringPredicate(103, "\U{0010}aaaaaaa\U{0006}\U{000C}a\U{000E}a\0a", "\U{0004}\U{0002}aaaaa\U{0008}aaa\n") == r0;
}
method {:test} Test123() {
var r0 := maxCommonSubstringLength("aaaaa\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}\n", "\U{000C}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}");
expect r0 <= |"aaaaa\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}\n"| && r0 <= |"\U{000C}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaa\U{0002}aaaaaaaaaa\U{0004}aaaa\U{0006}\n", "\U{000C}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}", r0);
}

// REPEAT 4 - TIME: 97.5828677 s

method {:test} Test124() {
var r0 := isPrefix("\U{0002}\0", "\U{0002}\0aaa\U{0006}a\U{0008}aa\U{0004}\na");
expect |"\U{0002}\0"| > |"\U{0002}\0aaa\U{0006}a\U{0008}aa\U{0004}\na"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0", "\U{0002}\0aaa\U{0006}a\U{0008}aa\U{0004}\na");
}
method {:test} Test125() {
var r0 := isPrefix("\U{0016}aaaa\U{000E}a\U{0012}\U{000C}a\0", "\U{0014}\U{0002}aaa\U{0006}\n\U{0010}aa\U{0008}\U{0004}");
expect |"\U{0016}aaaa\U{000E}a\U{0012}\U{000C}a\0"| > |"\U{0014}\U{0002}aaa\U{0006}\n\U{0010}aa\U{0008}\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0016}aaaa\U{000E}a\U{0012}\U{000C}a\0", "\U{0014}\U{0002}aaa\U{0006}\n\U{0010}aa\U{0008}\U{0004}");
}
method {:test} Test126() {
var r0 := isPrefix("\U{000E}aaaa\U{0004}aaaaaaa\U{0002}a", "\n\0aaa\U{0006}\U{000C}aaa\U{0008}");
expect |"\U{000E}aaaa\U{0004}aaaaaaa\U{0002}a"| > |"\n\0aaa\U{0006}\U{000C}aaa\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000E}aaaa\U{0004}aaaaaaa\U{0002}a", "\n\0aaa\U{0006}\U{000C}aaa\U{0008}");
}
method {:test} Test127() {
var r0 := isSubstring("\n\U{0006}\0\U{0004}aaaa", "\U{0008}\U{0002}aa\n\U{0006}\0\U{0004}aaaa");
expect r0 == isSubstringPredicate("\n\U{0006}\0\U{0004}aaaa", "\U{0008}\U{0002}aa\n\U{0006}\0\U{0004}aaaa");
}
method {:test} Test128() {
var r0 := isSubstring("\U{0008}aaaa\U{0004}aaa\U{0006}", "\U{0002}\0");
expect r0 == isSubstringPredicate("\U{0008}aaaa\U{0004}aaa\U{0006}", "\U{0002}\0");
}
method {:test} Test129() {
var r0 := haveCommonKSubstring(16, "a\0aaa\U{0006}aaa\na\U{0002}a\U{000E}aaaaaaaa\U{0014}a\U{0016}\U{0012}a\U{0010}aa", "\U{0018}aaaaa\U{0004}\U{0008}aaaaa\U{000C}aaaaaaaa\U{0014}a\U{0016}\U{0012}a\U{0010}aa");
expect |"a\0aaa\U{0006}aaa\na\U{0002}a\U{000E}aaaaaaaa\U{0014}a\U{0016}\U{0012}a\U{0010}aa"| < 16 || |"\U{0018}aaaaa\U{0004}\U{0008}aaaaa\U{000C}aaaaaaaa\U{0014}a\U{0016}\U{0012}a\U{0010}aa"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "a\0aaa\U{0006}aaa\na\U{0002}a\U{000E}aaaaaaaa\U{0014}a\U{0016}\U{0012}a\U{0010}aa", "\U{0018}aaaaa\U{0004}\U{0008}aaaaa\U{000C}aaaaaaaa\U{0014}a\U{0016}\U{0012}a\U{0010}aa") == r0;
}
method {:test} Test130() {
var r0 := haveCommonKSubstring(22, "a\0aaaaaaa\U{0004}a\U{000C}aa\U{0010}\U{0018}aaaa\U{0006}\U{001C}a\U{001A}aa\U{001E}", "\"aaaaaaaaaaaa\U{0012}\na\U{0016}\U{0014}\U{000E}aaaaaa\U{0008}a \U{0002}");
expect |"a\0aaaaaaa\U{0004}a\U{000C}aa\U{0010}\U{0018}aaaa\U{0006}\U{001C}a\U{001A}aa\U{001E}"| < 22 || |"\"aaaaaaaaaaaa\U{0012}\na\U{0016}\U{0014}\U{000E}aaaaaa\U{0008}a \U{0002}"| < 22 ==> !r0;
expect haveCommonKSubstringPredicate(22, "a\0aaaaaaa\U{0004}a\U{000C}aa\U{0010}\U{0018}aaaa\U{0006}\U{001C}a\U{001A}aa\U{001E}", "\"aaaaaaaaaaaa\U{0012}\na\U{0016}\U{0014}\U{000E}aaaaaa\U{0008}a \U{0002}") == r0;
}
method {:test} Test131() {
var r0 := haveCommonKSubstring(104, "\U{0004}\0", "\U{0006}\U{0002}aaa\U{0008}");
expect |"\U{0004}\0"| < 104 || |"\U{0006}\U{0002}aaa\U{0008}"| < 104 ==> !r0;
expect haveCommonKSubstringPredicate(104, "\U{0004}\0", "\U{0006}\U{0002}aaa\U{0008}") == r0;
}
method {:test} Test132() {
var r0 := maxCommonSubstringLength("aa\U{0002}aaaaaaaaaaaaaaa\U{0006}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaa\U{0008}\n");
expect r0 <= |"aa\U{0002}aaaaaaaaaaaaaaa\U{0006}"| && r0 <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaaa\U{0008}\n"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aa\U{0002}aaaaaaaaaaaaaaa\U{0006}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaa\U{0008}\n", r0);
}

// REPEAT 5 - TIME: 106.3337852 s

method {:test} Test133() {
var r0 := isPrefix("\U{0004}\0aaa\U{0008}a\U{0002}aa\naa\U{0006}aa", "\U{0004}\0aaa\U{0008}a\U{0002}aa\naa\U{0006}aa\U{000E}\U{000C}");
expect |"\U{0004}\0aaa\U{0008}a\U{0002}aa\naa\U{0006}aa"| > |"\U{0004}\0aaa\U{0008}a\U{0002}aa\naa\U{0006}aa\U{000E}\U{000C}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0aaa\U{0008}a\U{0002}aa\naa\U{0006}aa", "\U{0004}\0aaa\U{0008}a\U{0002}aa\naa\U{0006}aa\U{000E}\U{000C}");
}
method {:test} Test134() {
var r0 := isPrefix("aaa\U{0002}\U{000E}\U{0012}\U{0004}\U{0014}a\U{0010}\U{0018}\U{001A}", "\U{000C}\0aaaaa\U{0006}a\U{0016}a\U{0008}\n\U{001C}");
expect |"aaa\U{0002}\U{000E}\U{0012}\U{0004}\U{0014}a\U{0010}\U{0018}\U{001A}"| > |"\U{000C}\0aaaaa\U{0006}a\U{0016}a\U{0008}\n\U{001C}"| ==> !r0;
expect r0 == isPrefixPredicate("aaa\U{0002}\U{000E}\U{0012}\U{0004}\U{0014}a\U{0010}\U{0018}\U{001A}", "\U{000C}\0aaaaa\U{0006}a\U{0016}a\U{0008}\n\U{001C}");
}
method {:test} Test135() {
var r0 := isPrefix("aaaaaaaaaaaaa\U{000C}aaaaaaaa\U{0004}a\U{0010}a\naa", "a\0aaa\U{0002}a\U{0006}a\U{0008}a\U{0012}\U{000E}\U{0014}");
expect |"aaaaaaaaaaaaa\U{000C}aaaaaaaa\U{0004}a\U{0010}a\naa"| > |"a\0aaa\U{0002}a\U{0006}a\U{0008}a\U{0012}\U{000E}\U{0014}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaaaaaa\U{000C}aaaaaaaa\U{0004}a\U{0010}a\naa", "a\0aaa\U{0002}a\U{0006}a\U{0008}a\U{0012}\U{000E}\U{0014}");
}
method {:test} Test136() {
var r0 := isSubstring("a\0\U{0008}aa\U{0002}a\U{0004}\U{0006}", "\U{000C}aaaaaaaaaaaaaa\naa\0\U{0008}aa\U{0002}a\U{0004}\U{0006}");
expect r0 == isSubstringPredicate("a\0\U{0008}aa\U{0002}a\U{0004}\U{0006}", "\U{000C}aaaaaaaaaaaaaa\naa\0\U{0008}aa\U{0002}a\U{0004}\U{0006}");
}
method {:test} Test137() {
var r0 := isSubstring("\U{0006}aa\U{0002}aa", "\U{0004}\0aaa");
expect r0 == isSubstringPredicate("\U{0006}aa\U{0002}aa", "\U{0004}\0aaa");
}
method {:test} Test138() {
var r0 := haveCommonKSubstring(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa"| < 23 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 23 ==> !r0;
expect haveCommonKSubstringPredicate(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test139() {
var r0 := haveCommonKSubstring(23, "a\0aaaaaaa\U{000E}a\U{0012}a\U{0014}aaaaaaaa\U{0006}aaaa\U{0016}", "\U{0004}aaaaaa\naa\U{000C}aaaaaaaaaaa\U{0008}a\U{0010}aa\U{0002}\U{0018}");
expect |"a\0aaaaaaa\U{000E}a\U{0012}a\U{0014}aaaaaaaa\U{0006}aaaa\U{0016}"| < 23 || |"\U{0004}aaaaaa\naa\U{000C}aaaaaaaaaaa\U{0008}a\U{0010}aa\U{0002}\U{0018}"| < 23 ==> !r0;
expect haveCommonKSubstringPredicate(23, "a\0aaaaaaa\U{000E}a\U{0012}a\U{0014}aaaaaaaa\U{0006}aaaa\U{0016}", "\U{0004}aaaaaa\naa\U{000C}aaaaaaaaaaa\U{0008}a\U{0010}aa\U{0002}\U{0018}") == r0;
}
method {:test} Test140() {
var r0 := haveCommonKSubstring(105, "\U{000C}\U{0004}aaa\0aaa\naaaaaaaaa", "\U{0008}aaaa\U{0006}a\U{0002}");
expect |"\U{000C}\U{0004}aaa\0aaa\naaaaaaaaa"| < 105 || |"\U{0008}aaaa\U{0006}a\U{0002}"| < 105 ==> !r0;
expect haveCommonKSubstringPredicate(105, "\U{000C}\U{0004}aaa\0aaa\naaaaaaaaa", "\U{0008}aaaa\U{0006}a\U{0002}") == r0;
}
method {:test} Test141() {
var r0 := maxCommonSubstringLength("\U{0008}a\U{0002}aaaaa\U{0004}aaaaaaaaa\U{0006}", "\n\0aaaaaaaaaaaaaaaaaaaaa");
expect r0 <= |"\U{0008}a\U{0002}aaaaa\U{0004}aaaaaaaaa\U{0006}"| && r0 <= |"\n\0aaaaaaaaaaaaaaaaaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0008}a\U{0002}aaaaa\U{0004}aaaaaaaaa\U{0006}", "\n\0aaaaaaaaaaaaaaaaaaaaa", r0);
}

// REPEAT 6 - TIME: 115.5858929 s

method {:test} Test142() {
var r0 := isPrefix("a\0a\U{0002}\U{0008}\na\U{0010}a\U{0012}aa\U{000E}\U{0014}\U{000C}aa", "a\0a\U{0002}\U{0008}\na\U{0010}a\U{0012}aa\U{000E}\U{0014}\U{000C}aaa\U{0018}aaaa\U{0016}aaa\U{0004}\U{0006}a");
expect |"a\0a\U{0002}\U{0008}\na\U{0010}a\U{0012}aa\U{000E}\U{0014}\U{000C}aa"| > |"a\0a\U{0002}\U{0008}\na\U{0010}a\U{0012}aa\U{000E}\U{0014}\U{000C}aaa\U{0018}aaaa\U{0016}aaa\U{0004}\U{0006}a"| ==> !r0;
expect r0 == isPrefixPredicate("a\0a\U{0002}\U{0008}\na\U{0010}a\U{0012}aa\U{000E}\U{0014}\U{000C}aa", "a\0a\U{0002}\U{0008}\na\U{0010}a\U{0012}aa\U{000E}\U{0014}\U{000C}aaa\U{0018}aaaa\U{0016}aaa\U{0004}\U{0006}a");
}
method {:test} Test143() {
var r0 := isPrefix("\U{0016}aaa\0aaaa\U{0006}aa\U{000E}aaa\U{0014}", "a\U{0004}aa\U{0002}aaaa\U{000C}a\na\U{0010}\U{0012}\U{0008}a");
expect |"\U{0016}aaa\0aaaa\U{0006}aa\U{000E}aaa\U{0014}"| > |"a\U{0004}aa\U{0002}aaaa\U{000C}a\na\U{0010}\U{0012}\U{0008}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0016}aaa\0aaaa\U{0006}aa\U{000E}aaa\U{0014}", "a\U{0004}aa\U{0002}aaaa\U{000C}a\na\U{0010}\U{0012}\U{0008}a");
}
method {:test} Test144() {
var r0 := isPrefix("\U{0018}aaaa\U{000C}aa\U{0006}\U{0014}\U{0010}\U{0002}\U{000E}\U{0012}a", "\U{0016}\0aa\U{0004}\naaa\U{0008}");
expect |"\U{0018}aaaa\U{000C}aa\U{0006}\U{0014}\U{0010}\U{0002}\U{000E}\U{0012}a"| > |"\U{0016}\0aa\U{0004}\naaa\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0018}aaaa\U{000C}aa\U{0006}\U{0014}\U{0010}\U{0002}\U{000E}\U{0012}a", "\U{0016}\0aa\U{0004}\naaa\U{0008}");
}
method {:test} Test145() {
var r0 := isSubstring("\U{0008}\0\U{0004}a\U{000C}a\U{0006}", "\n\U{0002}\U{0008}\0\U{0004}a\U{000C}a\U{0006}");
expect r0 == isSubstringPredicate("\U{0008}\0\U{0004}a\U{000C}a\U{0006}", "\n\U{0002}\U{0008}\0\U{0004}a\U{000C}a\U{0006}");
}
method {:test} Test146() {
var r0 := isSubstring("\U{0018}aaaaaaaa\U{0014}aaaa\U{0008}a\U{0010}aa\U{0012}aaa\U{000C}\U{0006}aaaa\0", "\U{0004}aaaa\U{000E}aaaaaaaa\U{0016}a\naaaaaaaaaa\U{0002}a");
expect r0 == isSubstringPredicate("\U{0018}aaaaaaaa\U{0014}aaaa\U{0008}a\U{0010}aa\U{0012}aaa\U{000C}\U{0006}aaaa\0", "\U{0004}aaaa\U{000E}aaaaaaaa\U{0016}a\naaaaaaaaaa\U{0002}a");
}
method {:test} Test147() {
var r0 := haveCommonKSubstring(24, "\naaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\U{0004}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |"\naaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\U{0004}"| < 24 || |"\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaa\0"| < 24 ==> !r0;
expect haveCommonKSubstringPredicate(24, "\naaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0006}\U{0004}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaa\0") == r0;
}
method {:test} Test148() {
var r0 := haveCommonKSubstring(25, "\U{0004}aaaaaaaa\U{000C}aaaaaaaaaaaaaaaaaaa", "\U{0002}\0aaaaa\U{0008}aaaaa\U{000E}a\naaaaa\U{0006}aaaa");
expect |"\U{0004}aaaaaaaa\U{000C}aaaaaaaaaaaaaaaaaaa"| < 25 || |"\U{0002}\0aaaaa\U{0008}aaaaa\U{000E}a\naaaaa\U{0006}aaaa"| < 25 ==> !r0;
expect haveCommonKSubstringPredicate(25, "\U{0004}aaaaaaaa\U{000C}aaaaaaaaaaaaaaaaaaa", "\U{0002}\0aaaaa\U{0008}aaaaa\U{000E}a\naaaaa\U{0006}aaaa") == r0;
}
method {:test} Test149() {
var r0 := haveCommonKSubstring(106, "\U{0014}aaaaaaaaaaaaaa\U{0006}a\U{0004}aaa\U{0002}\naaaa\U{000E}\U{000C}", "\U{0012}aaaaaaaaaaaaa\0aaaaaaaaaaa\U{0008}\U{0010}");
expect |"\U{0014}aaaaaaaaaaaaaa\U{0006}a\U{0004}aaa\U{0002}\naaaa\U{000E}\U{000C}"| < 106 || |"\U{0012}aaaaaaaaaaaaa\0aaaaaaaaaaa\U{0008}\U{0010}"| < 106 ==> !r0;
expect haveCommonKSubstringPredicate(106, "\U{0014}aaaaaaaaaaaaaa\U{0006}a\U{0004}aaa\U{0002}\naaaa\U{000E}\U{000C}", "\U{0012}aaaaaaaaaaaaa\0aaaaaaaaaaa\U{0008}\U{0010}") == r0;
}
method {:test} Test150() {
var r0 := maxCommonSubstringLength("\U{0008}\U{0002}aaaaaaaaaaaaaaaaaa\U{0004}", "\n\0aaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <= |"\U{0008}\U{0002}aaaaaaaaaaaaaaaaaa\U{0004}"| && r0 <= |"\n\0aaaaaaaaaaaaaaaaa\U{0006}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0008}\U{0002}aaaaaaaaaaaaaaaaaa\U{0004}", "\n\0aaaaaaaaaaaaaaaaa\U{0006}", r0);
}

// REPEAT 7 - TIME: 124.569588 s

method {:test} Test151() {
var r0 := isPrefix("a\0aaaaaaaaa\U{0002}a\U{0006}a\n\U{0004}a", "a\0aaaaaaaaa\U{0002}a\U{0006}a\n\U{0004}a\U{0008}");
expect |"a\0aaaaaaaaa\U{0002}a\U{0006}a\n\U{0004}a"| > |"a\0aaaaaaaaa\U{0002}a\U{0006}a\n\U{0004}a\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaaaaaaaa\U{0002}a\U{0006}a\n\U{0004}a", "a\0aaaaaaaaa\U{0002}a\U{0006}a\n\U{0004}a\U{0008}");
}
method {:test} Test152() {
var r0 := isPrefix("aaaaaa\U{0008}aaaa\U{0010}\0aaa\U{0012}\U{0016}aaaaa\U{000E}aa\U{001A}a\U{0006}a", "\U{001C}\U{0004}aaaaaaa\U{000C}aa\U{0002}aaa\U{0014}aaaa\naaaaa\U{0018}aa");
expect |"aaaaaa\U{0008}aaaa\U{0010}\0aaa\U{0012}\U{0016}aaaaa\U{000E}aa\U{001A}a\U{0006}a"| > |"\U{001C}\U{0004}aaaaaaa\U{000C}aa\U{0002}aaa\U{0014}aaaa\naaaaa\U{0018}aa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaa\U{0008}aaaa\U{0010}\0aaa\U{0012}\U{0016}aaaaa\U{000E}aa\U{001A}a\U{0006}a", "\U{001C}\U{0004}aaaaaaa\U{000C}aa\U{0002}aaa\U{0014}aaaa\naaaaa\U{0018}aa");
}
method {:test} Test153() {
var r0 := isPrefix("aaaaa\U{0008}a\U{000E}aaa\U{000C}aaa\U{001A}a\na\U{0016}\U{0002}\U{0010}", "\U{001C}\0aaaaaaaa\U{0012}\U{0014}a\U{0004}\U{0018}aaa\U{0006}aa");
expect |"aaaaa\U{0008}a\U{000E}aaa\U{000C}aaa\U{001A}a\na\U{0016}\U{0002}\U{0010}"| > |"\U{001C}\0aaaaaaaa\U{0012}\U{0014}a\U{0004}\U{0018}aaa\U{0006}aa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaa\U{0008}a\U{000E}aaa\U{000C}aaa\U{001A}a\na\U{0016}\U{0002}\U{0010}", "\U{001C}\0aaaaaaaa\U{0012}\U{0014}a\U{0004}\U{0018}aaa\U{0006}aa");
}
method {:test} Test154() {
var r0 := isSubstring("\U{000E}aaaaaaa\U{0002}a\U{0004}\U{0006}a\n", "\U{000C}aaaa\0aaaaaa\U{0008}\U{000E}aaaaaaa\U{0002}a\U{0004}\U{0006}a\n");
expect r0 == isSubstringPredicate("\U{000E}aaaaaaa\U{0002}a\U{0004}\U{0006}a\n", "\U{000C}aaaa\0aaaaaa\U{0008}\U{000E}aaaaaaa\U{0002}a\U{0004}\U{0006}a\n");
}
method {:test} Test155() {
var r0 := isSubstring("\U{0004}\0aaa", "\U{0002}aaa");
expect r0 == isSubstringPredicate("\U{0004}\0aaa", "\U{0002}aaa");
}
method {:test} Test156() {
var r0 := haveCommonKSubstring(27, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 27 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 27 ==> !r0;
expect haveCommonKSubstringPredicate(27, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test157() {
var r0 := haveCommonKSubstring(28, "\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}\U{0004}aaaaaa\U{0008}", "\naaaaaaaaaaaa\U{0002}aaaaa\0aaaaaaaaaa");
expect |"\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}\U{0004}aaaaaa\U{0008}"| < 28 || |"\naaaaaaaaaaaa\U{0002}aaaaa\0aaaaaaaaaa"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}\U{0004}aaaaaa\U{0008}", "\naaaaaaaaaaaa\U{0002}aaaaa\0aaaaaaaaaa") == r0;
}
method {:test} Test158() {
var r0 := haveCommonKSubstring(107, "\naaaaaaaaaaaaaaaaaa\U{0006}\U{0004}aaaaaaa\U{0008}", "aaaaaaaaaaaaa\U{0002}\0aaaaaa");
expect |"\naaaaaaaaaaaaaaaaaa\U{0006}\U{0004}aaaaaaa\U{0008}"| < 107 || |"aaaaaaaaaaaaa\U{0002}\0aaaaaa"| < 107 ==> !r0;
expect haveCommonKSubstringPredicate(107, "\naaaaaaaaaaaaaaaaaa\U{0006}\U{0004}aaaaaaa\U{0008}", "aaaaaaaaaaaaa\U{0002}\0aaaaaa") == r0;
}
method {:test} Test159() {
var r0 := maxCommonSubstringLength("\U{0008}aaaaaaaaa\U{0002}aaaaaaaa\U{0006}aaa\U{0004}", "\na\0");
expect r0 <= |"\U{0008}aaaaaaaaa\U{0002}aaaaaaaa\U{0006}aaa\U{0004}"| && r0 <= |"\na\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0008}aaaaaaaaa\U{0002}aaaaaaaa\U{0006}aaa\U{0004}", "\na\0", r0);
}

// REPEAT 8 - TIME: 135.4150457 s

method {:test} Test160() {
var r0 := isPrefix("\U{000C}aaaaaa\U{0002}aaaaaaaaa\U{0008}a\0\U{0006}", "\U{000C}aaaaaa\U{0002}aaaaaaaaa\U{0008}a\0\U{0006}a\U{0004}\n");
expect |"\U{000C}aaaaaa\U{0002}aaaaaaaaa\U{0008}a\0\U{0006}"| > |"\U{000C}aaaaaa\U{0002}aaaaaaaaa\U{0008}a\0\U{0006}a\U{0004}\n"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}aaaaaa\U{0002}aaaaaaaaa\U{0008}a\0\U{0006}", "\U{000C}aaaaaa\U{0002}aaaaaaaaa\U{0008}a\0\U{0006}a\U{0004}\n");
}
method {:test} Test161() {
var r0 := isPrefix(" aaaaaa\naa\U{0008}\U{0014}a\U{0018}aaaa\U{0012}aa\U{0016}aaaaa\U{0010}\U{000E}", "\0\U{0002}aaaaaaa\U{000C}aaaa\U{0006}aaaaa\U{001E}\U{0004}\U{001A}a\U{001C}aaaa");
expect |" aaaaaa\naa\U{0008}\U{0014}a\U{0018}aaaa\U{0012}aa\U{0016}aaaaa\U{0010}\U{000E}"| > |"\0\U{0002}aaaaaaa\U{000C}aaaa\U{0006}aaaaa\U{001E}\U{0004}\U{001A}a\U{001C}aaaa"| ==> !r0;
expect r0 == isPrefixPredicate(" aaaaaa\naa\U{0008}\U{0014}a\U{0018}aaaa\U{0012}aa\U{0016}aaaaa\U{0010}\U{000E}", "\0\U{0002}aaaaaaa\U{000C}aaaa\U{0006}aaaaa\U{001E}\U{0004}\U{001A}a\U{001C}aaaa");
}
method {:test} Test162() {
var r0 := isPrefix("\naaaa\0a\U{0006}aaaaaaaaaa\U{0002}aaaaaaaaaa", "\U{0008}aaaaaaaaaaa\U{0004}");
expect |"\naaaa\0a\U{0006}aaaaaaaaaa\U{0002}aaaaaaaaaa"| > |"\U{0008}aaaaaaaaaaa\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\naaaa\0a\U{0006}aaaaaaaaaa\U{0002}aaaaaaaaaa", "\U{0008}aaaaaaaaaaa\U{0004}");
}
method {:test} Test163() {
var r0 := isSubstring("\U{0012}a\U{0010}aaaa\U{0004}aaa\U{0002}\n\0a\U{000E}", "\U{0014}aaaaaaaa\U{0006}a\U{0008}\U{000C}\U{0012}a\U{0010}aaaa\U{0004}aaa\U{0002}\n\0a\U{000E}");
expect r0 == isSubstringPredicate("\U{0012}a\U{0010}aaaa\U{0004}aaa\U{0002}\n\0a\U{000E}", "\U{0014}aaaaaaaa\U{0006}a\U{0008}\U{000C}\U{0012}a\U{0010}aaaa\U{0004}aaa\U{0002}\n\0a\U{000E}");
}
method {:test} Test164() {
var r0 := isSubstring("\U{0004}\0aaaaaaaaaaaaaaa", "\U{0002}aa");
expect r0 == isSubstringPredicate("\U{0004}\0aaaaaaaaaaaaaaa", "\U{0002}aa");
}
method {:test} Test165() {
var r0 := haveCommonKSubstring(29, "\U{0002}\U{0004}aaaaaaaaaaaaa\U{0008}\U{0006}aaaaaaaaaaaaa", "\0\U{0004}aaaaaaaaaaaaa\U{0008}\U{0006}aaaaaaaaaaaaa");
expect |"\U{0002}\U{0004}aaaaaaaaaaaaa\U{0008}\U{0006}aaaaaaaaaaaaa"| < 29 || |"\0\U{0004}aaaaaaaaaaaaa\U{0008}\U{0006}aaaaaaaaaaaaa"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\U{0002}\U{0004}aaaaaaaaaaaaa\U{0008}\U{0006}aaaaaaaaaaaaa", "\0\U{0004}aaaaaaaaaaaaa\U{0008}\U{0006}aaaaaaaaaaaaa") == r0;
}
method {:test} Test166() {
var r0 := haveCommonKSubstring(29, "\U{000C}\0aaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0004}aa", "\U{0002}aaaaaaaaaaaa\naaaa\U{0008}aaaaaaaaaa");
expect |"\U{000C}\0aaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0004}aa"| < 29 || |"\U{0002}aaaaaaaaaaaa\naaaa\U{0008}aaaaaaaaaa"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\U{000C}\0aaaaaaaaa\U{0006}aaaaaaaaaaaaaaa\U{0004}aa", "\U{0002}aaaaaaaaaaaa\naaaa\U{0008}aaaaaaaaaa") == r0;
}
method {:test} Test167() {
var r0 := haveCommonKSubstring(108, "\U{0010}\U{0002}aaaaaaa\na\U{000E}aaaaaaa\0\U{0006}aaaa", "\U{000C}aaaaa\U{0004}\U{0008}a");
expect |"\U{0010}\U{0002}aaaaaaa\na\U{000E}aaaaaaa\0\U{0006}aaaa"| < 108 || |"\U{000C}aaaaa\U{0004}\U{0008}a"| < 108 ==> !r0;
expect haveCommonKSubstringPredicate(108, "\U{0010}\U{0002}aaaaaaa\na\U{000E}aaaaaaa\0\U{0006}aaaa", "\U{000C}aaaaa\U{0004}\U{0008}a") == r0;
}
method {:test} Test168() {
var r0 := maxCommonSubstringLength("\U{0002}aa\U{0006}", "\U{0004}\0aaaaaaaaaaaaaaaaaaa\U{0008}");
expect r0 <= |"\U{0002}aa\U{0006}"| && r0 <= |"\U{0004}\0aaaaaaaaaaaaaaaaaaa\U{0008}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}aa\U{0006}", "\U{0004}\0aaaaaaaaaaaaaaaaaaa\U{0008}", r0);
}

// REPEAT 9 - TIME: 146.5733201 s

method {:test} Test169() {
var r0 := isPrefix("\U{0014}aaa\U{0004}\n\U{0006}aaaaaa\U{0010}a\U{000C}\U{0008}aaaa\U{0012}a", "\U{0014}aaa\U{0004}\n\U{0006}aaaaaa\U{0010}a\U{000C}\U{0008}aaaa\U{0012}a\U{0016}\U{000E}a\U{0002}a\0");
expect |"\U{0014}aaa\U{0004}\n\U{0006}aaaaaa\U{0010}a\U{000C}\U{0008}aaaa\U{0012}a"| > |"\U{0014}aaa\U{0004}\n\U{0006}aaaaaa\U{0010}a\U{000C}\U{0008}aaaa\U{0012}a\U{0016}\U{000E}a\U{0002}a\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0014}aaa\U{0004}\n\U{0006}aaaaaa\U{0010}a\U{000C}\U{0008}aaaa\U{0012}a", "\U{0014}aaa\U{0004}\n\U{0006}aaaaaa\U{0010}a\U{000C}\U{0008}aaaa\U{0012}a\U{0016}\U{000E}a\U{0002}a\0");
}
method {:test} Test170() {
var r0 := isPrefix("\0a", "\U{0002}aaaaaaaaaaaaa");
expect |"\0a"| > |"\U{0002}aaaaaaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\0a", "\U{0002}aaaaaaaaaaaaa");
}
method {:test} Test171() {
var r0 := isPrefix("\U{000C}aaaa\0a\U{0008}aaaa\U{0004}aaaaaaaa\U{0002}aaaa", "\naaaaaaaaa\U{0006}aaaaaaaaaaaaaa");
expect |"\U{000C}aaaa\0a\U{0008}aaaa\U{0004}aaaaaaaa\U{0002}aaaa"| > |"\naaaaaaaaa\U{0006}aaaaaaaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}aaaa\0a\U{0008}aaaa\U{0004}aaaaaaaa\U{0002}aaaa", "\naaaaaaaaa\U{0006}aaaaaaaaaaaaaa");
}
method {:test} Test172() {
var r0 := isSubstring("\U{0014}aaaaaa\U{0012}a\U{0008}\naaa\U{000C}a\U{0010}", "\U{0016}aaaa\U{0004}aaa\U{0006}\0\U{0002}\U{000E}\U{0014}aaaaaa\U{0012}a\U{0008}\naaa\U{000C}a\U{0010}");
expect r0 == isSubstringPredicate("\U{0014}aaaaaa\U{0012}a\U{0008}\naaa\U{000C}a\U{0010}", "\U{0016}aaaa\U{0004}aaa\U{0006}\0\U{0002}\U{000E}\U{0014}aaaaaa\U{0012}a\U{0008}\naaa\U{000C}a\U{0010}");
}
method {:test} Test173() {
var r0 := isSubstring("\U{0002}aaa", "\0aa");
expect r0 == isSubstringPredicate("\U{0002}aaa", "\0aa");
}
method {:test} Test174() {
var r0 := haveCommonKSubstring(30, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 30 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 30 ==> !r0;
expect haveCommonKSubstringPredicate(30, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test175() {
var r0 := haveCommonKSubstring(30, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 30 || |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 30 ==> !r0;
expect haveCommonKSubstringPredicate(30, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test176() {
var r0 := haveCommonKSubstring(109, "aaaaaaaaaa\U{0002}\U{0008}a\naaaaaaaaaa", "aaaaaaa\U{0004}aaaaa\U{000C}a\U{0006}aaaaaaa\0a");
expect |"aaaaaaaaaa\U{0002}\U{0008}a\naaaaaaaaaa"| < 109 || |"aaaaaaa\U{0004}aaaaa\U{000C}a\U{0006}aaaaaaa\0a"| < 109 ==> !r0;
expect haveCommonKSubstringPredicate(109, "aaaaaaaaaa\U{0002}\U{0008}a\naaaaaaaaaa", "aaaaaaa\U{0004}aaaaa\U{000C}a\U{0006}aaaaaaa\0a") == r0;
}
method {:test} Test177() {
var r0 := maxCommonSubstringLength("\U{0002}aaa\U{0004}aaaa\U{0008}aaaaaaaaa\n", "\U{000C}\0aaaaaaaaaaaa\U{0006}aaaaaaaaaa");
expect r0 <= |"\U{0002}aaa\U{0004}aaaa\U{0008}aaaaaaaaa\n"| && r0 <= |"\U{000C}\0aaaaaaaaaaaa\U{0006}aaaaaaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}aaa\U{0004}aaaa\U{0008}aaaaaaaaa\n", "\U{000C}\0aaaaaaaaaaaa\U{0006}aaaaaaaaaa", r0);
}

// REPEAT 10 - TIME: 158.5754131 s

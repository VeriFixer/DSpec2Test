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

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
  if |pre| != |str| {
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

method {:test} Test14() {
var r0 := isPrefix("a\0aaaaa\U{0004}aaaaaaa\U{0002}", "a\0aaaaa\U{0004}aaaaaaa\U{0002}a");
expect |"a\0aaaaa\U{0004}aaaaaaa\U{0002}"| > |"a\0aaaaa\U{0004}aaaaaaa\U{0002}a"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaaaa\U{0004}aaaaaaa\U{0002}", "a\0aaaaa\U{0004}aaaaaaa\U{0002}a");
}
method {:test} Test15() {
var r0 := isPrefix("\U{0004}\U{0006}a\U{0002}", "\U{0004}\U{0006}a\0");
expect |"\U{0004}\U{0006}a\U{0002}"| > |"\U{0004}\U{0006}a\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\U{0006}a\U{0002}", "\U{0004}\U{0006}a\0");
}
method {:test} Test16() {
var r0 := isPrefix("a\0aaaaaaa\U{0002}\U{0004}", "aaaaaaaaa\U{0006}");
expect |"a\0aaaaaaa\U{0002}\U{0004}"| > |"aaaaaaaaa\U{0006}"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaaaaaa\U{0002}\U{0004}", "aaaaaaaaa\U{0006}");
}
method {:test} Test17() {
var r0 := isSubstring("aa\U{0002}", "\U{0004}\0a");
expect r0 == isSubstringPredicate("aa\U{0002}", "\U{0004}\0a");
}
method {:test} Test18() {
var r0 := isSubstring("", "aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("", "aaaaaaaaaaaa");
}
method {:test} Test19() {
var r0 := isSubstring("a\0a", "\U{0002}a");
expect r0 == isSubstringPredicate("a\0a", "\U{0002}a");
}
method {:test} Test20() {
var r0 := haveCommonKSubstring(3, "aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0006}", "a\0aaaaa\U{0004}");
expect |"aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0006}"| < 3 || |"a\0aaaaa\U{0004}"| < 3 ==> !r0;
expect haveCommonKSubstringPredicate(3, "aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0006}", "a\0aaaaa\U{0004}") == r0;
}
method {:test} Test21() {
var r0 := haveCommonKSubstring(6, "aaaaaaaaaaaa", "aaaaaaaa");
expect |"aaaaaaaaaaaa"| < 6 || |"aaaaaaaa"| < 6 ==> !r0;
expect haveCommonKSubstringPredicate(6, "aaaaaaaaaaaa", "aaaaaaaa") == r0;
}
method {:test} Test22() {
var r0 := haveCommonKSubstring(9, "\U{0004}\U{0002}aaaaaaa", "aaaaaaa\0");
expect |"\U{0004}\U{0002}aaaaaaa"| < 9 || |"aaaaaaa\0"| < 9 ==> !r0;
expect haveCommonKSubstringPredicate(9, "\U{0004}\U{0002}aaaaaaa", "aaaaaaa\0") == r0;
}
method {:test} Test23() {
var r0 := haveCommonKSubstring(4, "a\0\U{0002}", "\U{0004}a");
expect |"a\0\U{0002}"| < 4 || |"\U{0004}a"| < 4 ==> !r0;
expect haveCommonKSubstringPredicate(4, "a\0\U{0002}", "\U{0004}a") == r0;
}
method {:test} Test24() {
var r0 := maxCommonSubstringLength("aa\0", "a\U{0002}");
expect r0 <= |"aa\0"| && r0 <= |"a\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aa\0", "a\U{0002}", r0);
}
method {:test} Test26() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaa\0", "a\U{0002}");
expect r0 <= |"aaaaaaaaaaaa\0"| && r0 <= |"a\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaa\0", "a\U{0002}", r0);
}
method {:test} Test27() {
var r0 := maxCommonSubstringLength("aaa", "a\0");
expect r0 <= |"aaa"| && r0 <= |"a\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaa", "a\0", r0);
}

// REPEAT 2 - TIME: 15.2707325 s

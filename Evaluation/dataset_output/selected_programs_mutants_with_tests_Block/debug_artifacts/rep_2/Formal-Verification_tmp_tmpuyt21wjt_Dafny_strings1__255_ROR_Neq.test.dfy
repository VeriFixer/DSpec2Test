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
var r0 := isPrefix("aaa", "aaa");
expect |"aaa"| > |"aaa"| ==> !r0;
expect r0 == isPrefixPredicate("aaa", "aaa");
}
method {:test} Test15() {
var r0 := isPrefix("\U{0006}\0\U{0004}", "\U{0006}\U{0002}\U{0004}");
expect |"\U{0006}\0\U{0004}"| > |"\U{0006}\U{0002}\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\0\U{0004}", "\U{0006}\U{0002}\U{0004}");
}
method {:test} Test16() {
var r0 := isPrefix("\U{0006}\U{0002}\U{0004}", "\U{0008}\0");
expect |"\U{0006}\U{0002}\U{0004}"| > |"\U{0008}\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\U{0002}\U{0004}", "\U{0008}\0");
}
method {:test} Test17() {
var r0 := isSubstring("aa\U{0002}", "\U{0004}\0a");
expect r0 == isSubstringPredicate("aa\U{0002}", "\U{0004}\0a");
}
method {:test} Test18() {
var r0 := isSubstring("", "\U{0002}\0");
expect r0 == isSubstringPredicate("", "\U{0002}\0");
}
method {:test} Test19() {
var r0 := isSubstring("\U{0002}aaaaaaaaa\0aa", "aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0002}aaaaaaaaa\0aa", "aaaaaaaaaaaa");
}
method {:test} Test20() {
var r0 := haveCommonKSubstring(3, "\U{0006}\0\U{0004}", "a\U{0002}a");
expect |"\U{0006}\0\U{0004}"| < 3 || |"a\U{0002}a"| < 3 ==> !r0;
expect haveCommonKSubstringPredicate(3, "\U{0006}\0\U{0004}", "a\U{0002}a") == r0;
}
method {:test} Test21() {
var r0 := haveCommonKSubstring(5, "aaaaaaaaaaaa", "aaaaaaaa");
expect |"aaaaaaaaaaaa"| < 5 || |"aaaaaaaa"| < 5 ==> !r0;
expect haveCommonKSubstringPredicate(5, "aaaaaaaaaaaa", "aaaaaaaa") == r0;
}
method {:test} Test22() {
var r0 := haveCommonKSubstring(3, "\U{0004}\U{0002}", "\U{0006}\0");
expect |"\U{0004}\U{0002}"| < 3 || |"\U{0006}\0"| < 3 ==> !r0;
expect haveCommonKSubstringPredicate(3, "\U{0004}\U{0002}", "\U{0006}\0") == r0;
}
method {:test} Test23() {
var r0 := maxCommonSubstringLength("aaa", "a\0");
expect r0 <= |"aaa"| && r0 <= |"a\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaa", "a\0", r0);
}
method {:test} Test25() {
var r0 := maxCommonSubstringLength("a\U{0002}a\U{0006}", "a\0aaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <= |"a\U{0002}a\U{0006}"| && r0 <= |"a\0aaaaaaaaaaaaaaaaa\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\U{0002}a\U{0006}", "a\0aaaaaaaaaaaaaaaaa\U{0004}", r0);
}
method {:test} Test26() {
var r0 := maxCommonSubstringLength("aa\0", "a\U{0002}");
expect r0 <= |"aa\0"| && r0 <= |"a\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aa\0", "a\U{0002}", r0);
}

// REPEAT 2 - TIME: 14.4958209 s

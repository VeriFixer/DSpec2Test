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

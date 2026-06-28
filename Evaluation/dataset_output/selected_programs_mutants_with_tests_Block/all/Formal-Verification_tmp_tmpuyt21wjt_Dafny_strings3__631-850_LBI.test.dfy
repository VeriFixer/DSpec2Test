// Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings3.dfy

predicate isPrefixPred(pre: string, str: string)
{
  |pre| <= |str| &&
  pre == str[..|pre|]
}

predicate isNotPrefixPred(pre: string, str: string)
{
  |pre| > |str| || pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre: string, str: string)
  ensures isPrefixPred(pre, str) <==> !isNotPrefixPred(pre, str)
  ensures !isPrefixPred(pre, str) <==> isNotPrefixPred(pre, str)
{
}

method {:testEntry} isPrefix(pre: string, str: string) returns (res: bool)
  ensures !res <==> isNotPrefixPred(pre, str)
  ensures res <==> isPrefixPred(pre, str)
{
  if |pre| > |str| {
    return false;
  }
  var i := 0;
  while i < |pre|
    invariant 0 <= i <= |pre|
    invariant forall j :: 0 <= j < i ==> pre[j] == str[j]
    decreases |pre| - i
  {
    break;
    if pre[i] != str[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

predicate isSubstringPred(sub: string, str: string)
{
  exists i :: 
    0 <= i <= |str| &&
    isPrefixPred(sub, str[i..])
}

predicate isNotSubstringPred(sub: string, str: string)
{
  forall i :: 
    0 <= i <= |str| ==>
      isNotPrefixPred(sub, str[i..])
}

lemma SubstringNegationLemma(sub: string, str: string)
  ensures isSubstringPred(sub, str) <==> !isNotSubstringPred(sub, str)
  ensures !isSubstringPred(sub, str) <==> isNotSubstringPred(sub, str)
{
}

method {:testEntry} isSubstring(sub: string, str: string) returns (res: bool)
  ensures res <==> isSubstringPred(sub, str)
{
  if |sub| > |str| {
    return false;
  }
  var i := |str| - |sub|;
  while i >= 0
    invariant i >= -1
    invariant forall j :: i < j <= |str| - |sub| ==> !isPrefixPred(sub, str[j..])
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

predicate haveCommonKSubstringPred(k: nat, str1: string, str2: string)
{
  exists i1, j1 :: 
    0 <= i1 <= |str1| - k &&
    j1 == i1 + k &&
    isSubstringPred(str1[i1 .. j1], str2)
}

predicate haveNotCommonKSubstringPred(k: nat, str1: string, str2: string)
{
  forall i1, j1 :: 
    0 <= i1 <= |str1| - k &&
    j1 == i1 + k ==>
      isNotSubstringPred(str1[i1 .. j1], str2)
}

lemma commonKSubstringLemma(k: nat, str1: string, str2: string)
  ensures haveCommonKSubstringPred(k, str1, str2) <==> !haveNotCommonKSubstringPred(k, str1, str2)
  ensures !haveCommonKSubstringPred(k, str1, str2) <==> haveNotCommonKSubstringPred(k, str1, str2)
{
}

method {:testEntry} haveCommonKSubstring(k: nat, str1: string, str2: string)
    returns (found: bool)
  ensures found <==> haveCommonKSubstringPred(k, str1, str2)
{
  if |str1| < k || |str2| < k {
    return false;
  }
  var i := |str1| - k;
  while i >= 0
    invariant i >= -1
    invariant forall j, t :: i < j <= |str1| - k && t == j + k ==> !isSubstringPred(str1[j .. t], str2)
    decreases i
  {
    var t := i + k;
    var isSub := isSubstring(str1[i .. t], str2);
    if isSub {
      return true;
    }
    i := i - 1;
  }
  return false;
}

method {:testEntry} maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  requires |str1| <= |str2|
  ensures forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
  ensures haveCommonKSubstringPred(len, str1, str2)
{
  var i := |str1|;
  while i > 0
    invariant i >= 0
    invariant forall j :: i < j <= |str1| ==> !haveCommonKSubstringPred(j, str1, str2)
    decreases i
  {
    var ans := haveCommonKSubstring(i, str1, str2);
    if ans {
      return i;
    }
    i := i - 1;
  }
  assert i == 0;
  assert isPrefixPred(str1[0 .. 0], str2[0..]);
  return 0;
}


method {:test} Test0() {
var r0 := isPrefix("a", "a");
expect !r0 <==> isNotPrefixPred("a", "a");
expect r0 <==> isPrefixPred("a", "a");
}
method {:test} Test1() {
var r0 := isPrefix("aaaaaaaa\0", "aaaaaaaa\U{0002}");
expect !r0 <==> isNotPrefixPred("aaaaaaaa\0", "aaaaaaaa\U{0002}");
expect r0 <==> isPrefixPred("aaaaaaaa\0", "aaaaaaaa\U{0002}");
}
method {:test} Test2() {
var r0 := isPrefix("aa", "a");
expect !r0 <==> isNotPrefixPred("aa", "a");
expect r0 <==> isPrefixPred("aa", "a");
}
method {:test} Test3() {
var r0 := isSubstring("a", "a");
expect r0 <==> isSubstringPred("a", "a");
}
method {:test} Test4() {
var r0 := isSubstring("aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test5() {
var r0 := isSubstring("aa", "a");
expect r0 <==> isSubstringPred("aa", "a");
}
method {:test} Test6() {
var r0 := haveCommonKSubstring(1, "a", "a");
expect r0 <==> haveCommonKSubstringPred(1, "a", "a");
}
method {:test} Test7() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaa", "aaa");
expect r0 <==> haveCommonKSubstringPred(1, "aaaaaaaaaaa", "aaa");
}
method {:test} Test8() {
var r0 := haveCommonKSubstring(2, "aa", "a");
expect r0 <==> haveCommonKSubstringPred(2, "aa", "a");
}
method {:test} Test9() {
var r0 := haveCommonKSubstring(2, "a", "");
expect r0 <==> haveCommonKSubstringPred(2, "a", "");
}
method {:test} Test10() {
expect |"a"| <= |"a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("a", "a");
expect forall k :: r0 < k <= |"a"| ==> !haveCommonKSubstringPred(k, "a", "a");
expect haveCommonKSubstringPred(r0, "a", "a");
}
method {:test} Test12() {
expect |"aaaaaaaaaa"| <= |"aaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaa", "aaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaa", "aaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaa", "aaaaaaaaaaaaaaa");
}

// REPEAT 1 - TIME: 9.7663392 s

method {:test} Test14() {
var r0 := isPrefix("\U{0006}\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}\0");
expect !r0 <==> isNotPrefixPred("\U{0006}\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}\0");
expect r0 <==> isPrefixPred("\U{0006}\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}\0");
}
method {:test} Test15() {
var r0 := isPrefix("\0\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}");
expect !r0 <==> isNotPrefixPred("\0\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}");
expect r0 <==> isPrefixPred("\0\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}");
}
method {:test} Test16() {
var r0 := isPrefix("\U{0002}aaaaaaaaa\U{0004}", "a\0aaaaaaa\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{0002}aaaaaaaaa\U{0004}", "a\0aaaaaaa\U{0006}");
expect r0 <==> isPrefixPred("\U{0002}aaaaaaaaa\U{0004}", "a\0aaaaaaa\U{0006}");
}
method {:test} Test17() {
var r0 := isSubstring("aa\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaa", "a\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> isSubstringPred("aa\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaaaa", "a\0aaaaaaaaaaaaaaaaaaaaaaa\U{0006}");
}
method {:test} Test18() {
var r0 := isSubstring("aaa\U{0004}aaaaaaaaaaaaaaa\U{0002}", "a\0aaa\U{0004}aaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> isSubstringPred("aaa\U{0004}aaaaaaaaaaaaaaa\U{0002}", "a\0aaa\U{0004}aaaaaaaaaaaaaaa\U{0002}");
}
method {:test} Test19() {
var r0 := isSubstring("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "a\0aaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <==> isSubstringPred("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "a\0aaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
}
method {:test} Test20() {
var r0 := haveCommonKSubstring(3, "aa\0aaaaaaaaaaaaa\U{0004}", "\U{0002}aa");
expect r0 <==> haveCommonKSubstringPred(3, "aa\0aaaaaaaaaaaaa\U{0004}", "\U{0002}aa");
}
method {:test} Test21() {
var r0 := haveCommonKSubstring(6, "a\U{0002}aaaaaaaaaa", "aaaaaaaaaaaaaa\0aaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(6, "a\U{0002}aaaaaaaaaa", "aaaaaaaaaaaaaa\0aaaaaaaaaaaa");
}
method {:test} Test22() {
var r0 := haveCommonKSubstring(3, "a\0aaaaaaaaa\U{0002}", "\U{0004}a");
expect r0 <==> haveCommonKSubstringPred(3, "a\0aaaaaaaaa\U{0002}", "\U{0004}a");
}
method {:test} Test23() {
var r0 := haveCommonKSubstring(4, "\U{0006}a\U{0002}", "a\0a\U{0004}");
expect r0 <==> haveCommonKSubstringPred(4, "\U{0006}a\U{0002}", "a\0a\U{0004}");
}
method {:test} Test24() {
expect |"\U{0002}a"| <= |"\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}a", "\U{0004}\0");
expect forall k :: r0 < k <= |"\U{0002}a"| ==> !haveCommonKSubstringPred(k, "\U{0002}a", "\U{0004}\0");
expect haveCommonKSubstringPred(r0, "\U{0002}a", "\U{0004}\0");
}
method {:test} Test26() {
expect |"\0a"| <= |"aaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0a", "aaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\0a"| ==> !haveCommonKSubstringPred(k, "\0a", "aaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\0a", "aaaaaaaaaaaaaaaa");
}
method {:test} Test27() {
expect |"aaaaaaaaaaaa\0"| <= |"aaaaaaaaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaa\0", "aaaaaaaaaaaaaaa\U{0002}");
expect forall k :: r0 < k <= |"aaaaaaaaaaaa\0"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaa\0", "aaaaaaaaaaaaaaa\U{0002}");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaa\0", "aaaaaaaaaaaaaaa\U{0002}");
}

// REPEAT 2 - TIME: 16.2087891 s

method {:test} Test28() {
var r0 := isPrefix("\U{0006}\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}\U{0008}aaaaaaaaaaaaaaaaa\0aaaaaaa");
expect !r0 <==> isNotPrefixPred("\U{0006}\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}\U{0008}aaaaaaaaaaaaaaaaa\0aaaaaaa");
expect r0 <==> isPrefixPred("\U{0006}\U{0002}\U{0004}", "\U{0006}\U{0002}\U{0004}\U{0008}aaaaaaaaaaaaaaaaa\0aaaaaaa");
}
method {:test} Test29() {
var r0 := isPrefix("\U{0004}\U{0006}a\U{0002}a", "\U{0004}\0aaaa");
expect !r0 <==> isNotPrefixPred("\U{0004}\U{0006}a\U{0002}a", "\U{0004}\0aaaa");
expect r0 <==> isPrefixPred("\U{0004}\U{0006}a\U{0002}a", "\U{0004}\0aaaa");
}
method {:test} Test30() {
var r0 := isPrefix("\U{0008}\0a\U{0002}aaaaaaaa", "\U{0004}aaaaaaaaa\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{0008}\0a\U{0002}aaaaaaaa", "\U{0004}aaaaaaaaa\U{0006}");
expect r0 <==> isPrefixPred("\U{0008}\0a\U{0002}aaaaaaaa", "\U{0004}aaaaaaaaa\U{0006}");
}
method {:test} Test31() {
var r0 := isSubstring("\U{000C}aaaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}\U{0006}", "\n\0aaaaaaaaaaaaaaaaaaaaaa\U{0008}aa");
expect r0 <==> isSubstringPred("\U{000C}aaaaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}\U{0006}", "\n\0aaaaaaaaaaaaaaaaaaaaaa\U{0008}aa");
}
method {:test} Test32() {
var r0 := isSubstring("\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}", "\U{0006}a\0a\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}");
expect r0 <==> isSubstringPred("\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}", "\U{0006}a\0a\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0004}");
}
method {:test} Test33() {
var r0 := isSubstring("\naaaaa\U{0002}aaaaaaaaaaaaa\U{0004}aaaaa", "\U{0008}\0aaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> isSubstringPred("\naaaaa\U{0002}aaaaaaaaaaaaa\U{0004}aaaaa", "\U{0008}\0aaaaaaaaaaaaaaaaaaaa\U{0006}");
}
method {:test} Test34() {
var r0 := haveCommonKSubstring(7, "aaaaaaaaaaaa\U{0002}", "aaaaaaaaaaaaaaaa\0aaaaaaaaaaa\U{0004}");
expect r0 <==> haveCommonKSubstringPred(7, "aaaaaaaaaaaa\U{0002}", "aaaaaaaaaaaaaaaa\0aaaaaaaaaaa\U{0004}");
}
method {:test} Test35() {
var r0 := haveCommonKSubstring(7, "aaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(7, "aaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test36() {
var r0 := haveCommonKSubstring(7, "\U{0008}aaaaa\U{0002}", "\U{0006}a\0\U{0004}");
expect r0 <==> haveCommonKSubstringPred(7, "\U{0008}aaaaa\U{0002}", "\U{0006}a\0\U{0004}");
}
method {:test} Test37() {
var r0 := haveCommonKSubstring(7, "\na\U{0002}a", "\U{0006}\0\U{0004}a\U{0008}");
expect r0 <==> haveCommonKSubstringPred(7, "\na\U{0002}a", "\U{0006}\0\U{0004}a\U{0008}");
}
method {:test} Test38() {
expect |"\U{0002}\0"| <= |"\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}\0", "\U{0004}a");
expect forall k :: r0 < k <= |"\U{0002}\0"| ==> !haveCommonKSubstringPred(k, "\U{0002}\0", "\U{0004}a");
expect haveCommonKSubstringPred(r0, "\U{0002}\0", "\U{0004}a");
}
method {:test} Test40() {
expect |"\U{0002}\0a"| <= |"\U{0004}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}\0a", "\U{0004}aa");
expect forall k :: r0 < k <= |"\U{0002}\0a"| ==> !haveCommonKSubstringPred(k, "\U{0002}\0a", "\U{0004}aa");
expect haveCommonKSubstringPred(r0, "\U{0002}\0a", "\U{0004}aa");
}
method {:test} Test41() {
expect |"\U{0004}\U{0002}a"| <= |"\U{0006}a\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}\U{0002}a", "\U{0006}a\0");
expect forall k :: r0 < k <= |"\U{0004}\U{0002}a"| ==> !haveCommonKSubstringPred(k, "\U{0004}\U{0002}a", "\U{0006}a\0");
expect haveCommonKSubstringPred(r0, "\U{0004}\U{0002}a", "\U{0006}a\0");
}

// REPEAT 3 - TIME: 22.7040065 s

method {:test} Test42() {
var r0 := isPrefix("\U{0006}\0aaaaaa\U{0002}\U{000C}a\U{0008}\U{000E}", "\U{0006}\0aaaaaa\U{0002}\U{000C}a\U{0008}\U{000E}\U{0004}aaa\naaaaaaaaaaa\U{0010}");
expect !r0 <==> isNotPrefixPred("\U{0006}\0aaaaaa\U{0002}\U{000C}a\U{0008}\U{000E}", "\U{0006}\0aaaaaa\U{0002}\U{000C}a\U{0008}\U{000E}\U{0004}aaa\naaaaaaaaaaa\U{0010}");
expect r0 <==> isPrefixPred("\U{0006}\0aaaaaa\U{0002}\U{000C}a\U{0008}\U{000E}", "\U{0006}\0aaaaaa\U{0002}\U{000C}a\U{0008}\U{000E}\U{0004}aaa\naaaaaaaaaaa\U{0010}");
}
method {:test} Test43() {
var r0 := isPrefix("a\U{0002}\U{0004}aaaaa\U{0006}\U{000C}aa\U{0010}", "a\U{0002}\0aaa\na\U{0006}a\U{0008}\U{000E}\U{0010}");
expect !r0 <==> isNotPrefixPred("a\U{0002}\U{0004}aaaaa\U{0006}\U{000C}aa\U{0010}", "a\U{0002}\0aaa\na\U{0006}a\U{0008}\U{000E}\U{0010}");
expect r0 <==> isPrefixPred("a\U{0002}\U{0004}aaaaa\U{0006}\U{000C}aa\U{0010}", "a\U{0002}\0aaa\na\U{0006}a\U{0008}\U{000E}\U{0010}");
}
method {:test} Test44() {
var r0 := isPrefix("\U{0006}aaaaaaaa\U{0004}\0aa", "\U{0008}aa\U{0002}a");
expect !r0 <==> isNotPrefixPred("\U{0006}aaaaaaaa\U{0004}\0aa", "\U{0008}aa\U{0002}a");
expect r0 <==> isPrefixPred("\U{0006}aaaaaaaa\U{0004}\0aa", "\U{0008}aa\U{0002}a");
}
method {:test} Test45() {
var r0 := isSubstring("aa\U{0002}aaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}\U{000E}", "\U{0010}\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n");
expect r0 <==> isSubstringPred("aa\U{0002}aaaaaaaaaaaaaaaaaa\U{0004}aaa\U{0008}\U{000C}\U{000E}", "\U{0010}\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n");
}
method {:test} Test46() {
var r0 := isSubstring("\0\U{0004}aaaaaaaaa", "\U{0002}\0\U{0004}aaaaaaaaa");
expect r0 <==> isSubstringPred("\0\U{0004}aaaaaaaaa", "\U{0002}\0\U{0004}aaaaaaaaa");
}
method {:test} Test47() {
var r0 := isSubstring("\U{0002}aa", "\U{0004}\0");
expect r0 <==> isSubstringPred("\U{0002}aa", "\U{0004}\0");
}
method {:test} Test48() {
var r0 := haveCommonKSubstring(8, "aaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(8, "aaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test50() {
var r0 := haveCommonKSubstring(8, "\U{000E}aaaaaaaaaa\U{0008}a\naaa\U{000C}", "\U{0010}\0a\U{0004}\U{0006}\U{0002}");
expect r0 <==> haveCommonKSubstringPred(8, "\U{000E}aaaaaaaaaa\U{0008}a\naaa\U{000C}", "\U{0010}\0a\U{0004}\U{0006}\U{0002}");
}
method {:test} Test51() {
var r0 := haveCommonKSubstring(9, "\U{0006}\U{0002}aaa\U{000C}a\U{000E}", "\U{0010}\0a\n\U{0004}\U{0008}");
expect r0 <==> haveCommonKSubstringPred(9, "\U{0006}\U{0002}aaa\U{000C}a\U{000E}", "\U{0010}\0a\n\U{0004}\U{0008}");
}
method {:test} Test52() {
expect |"\U{0004}aa\U{0006}"| <= |"\U{0008}\0\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aa\U{0006}", "\U{0008}\0\U{0002}a");
expect forall k :: r0 < k <= |"\U{0004}aa\U{0006}"| ==> !haveCommonKSubstringPred(k, "\U{0004}aa\U{0006}", "\U{0008}\0\U{0002}a");
expect haveCommonKSubstringPred(r0, "\U{0004}aa\U{0006}", "\U{0008}\0\U{0002}a");
}
method {:test} Test54() {
expect |""| <= |""|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("", "");
expect forall k :: r0 < k <= |""| ==> !haveCommonKSubstringPred(k, "", "");
expect haveCommonKSubstringPred(r0, "", "");
}
method {:test} Test55() {
expect |"\U{0004}aaaaaaaaa\U{0002}"| <= |"aa\0aaaa\U{0006}aaaaaa\U{0008}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaaaaaa\U{0002}", "aa\0aaaa\U{0006}aaaaaa\U{0008}a");
expect forall k :: r0 < k <= |"\U{0004}aaaaaaaaa\U{0002}"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaaaaaa\U{0002}", "aa\0aaaa\U{0006}aaaaaa\U{0008}a");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaaaaaa\U{0002}", "aa\0aaaa\U{0006}aaaaaa\U{0008}a");
}

// REPEAT 4 - TIME: 30.53644 s

method {:test} Test56() {
var r0 := isPrefix("\U{0002}aa\0", "\U{0002}aa\0\U{0004}aaaaa");
expect !r0 <==> isNotPrefixPred("\U{0002}aa\0", "\U{0002}aa\0\U{0004}aaaaa");
expect r0 <==> isPrefixPred("\U{0002}aa\0", "\U{0002}aa\0\U{0004}aaaaa");
}
method {:test} Test57() {
var r0 := isPrefix("\U{0010}\U{000E}\U{0004}a\0aaaaaa\n", "\U{0012}\U{000E}a\U{0008}a\U{0006}aaa\U{000C}a\naaaaaaa\U{0002}aaaaa");
expect !r0 <==> isNotPrefixPred("\U{0010}\U{000E}\U{0004}a\0aaaaaa\n", "\U{0012}\U{000E}a\U{0008}a\U{0006}aaa\U{000C}a\naaaaaaa\U{0002}aaaaa");
expect r0 <==> isPrefixPred("\U{0010}\U{000E}\U{0004}a\0aaaaaa\n", "\U{0012}\U{000E}a\U{0008}a\U{0006}aaa\U{000C}a\naaaaaaa\U{0002}aaaaa");
}
method {:test} Test58() {
var r0 := isPrefix("\naaaaaaaa\U{0004}\U{0002}a", "\U{0008}\0a\U{0006}aa");
expect !r0 <==> isNotPrefixPred("\naaaaaaaa\U{0004}\U{0002}a", "\U{0008}\0a\U{0006}aa");
expect r0 <==> isPrefixPred("\naaaaaaaa\U{0004}\U{0002}a", "\U{0008}\0a\U{0006}aa");
}
method {:test} Test59() {
var r0 := isSubstring("\U{0016}aaaaaa\U{0002}aaaaaaaaaaaa\naaa\U{0006}\U{0012}\U{0010}", "\U{0014}\0aaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{000E}a\U{000C}\U{0008}");
expect r0 <==> isSubstringPred("\U{0016}aaaaaa\U{0002}aaaaaaaaaaaa\naaa\U{0006}\U{0012}\U{0010}", "\U{0014}\0aaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{000E}a\U{000C}\U{0008}");
}
method {:test} Test60() {
var r0 := isSubstring("\U{0004}aaaa\U{0002}a", "\0aaaaaaaa\U{0004}aaaa\U{0002}aaaaaa");
expect r0 <==> isSubstringPred("\U{0004}aaaa\U{0002}a", "\0aaaaaaaa\U{0004}aaaa\U{0002}aaaaaa");
}
method {:test} Test61() {
var r0 := isSubstring("\U{0006}aaaaaaaaaa\U{0002}aa", "\U{0004}\0aaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0006}aaaaaaaaaa\U{0002}aa", "\U{0004}\0aaaaaaaaaaa");
}
method {:test} Test62() {
var r0 := haveCommonKSubstring(10, "aaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(10, "aaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test63() {
var r0 := haveCommonKSubstring(12, "aaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(12, "aaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test64() {
var r0 := haveCommonKSubstring(28, "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaa\0aaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(28, "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaa\0aaaaaaaaaaaaaaaaaaa");
}
method {:test} Test65() {
var r0 := haveCommonKSubstring(21, "aaaaaaa\U{0012}aaa\U{0016}a\U{001A}aa\U{0004}\U{0018}\U{0014}\U{0008}", "\U{001E}\U{0002}a\U{000C}\U{000E}a\naaaa\0aaaa\U{0010}aaaaaaa\U{0006}aa\U{001C}a");
expect r0 <==> haveCommonKSubstringPred(21, "aaaaaaa\U{0012}aaa\U{0016}a\U{001A}aa\U{0004}\U{0018}\U{0014}\U{0008}", "\U{001E}\U{0002}a\U{000C}\U{000E}a\naaaa\0aaaa\U{0010}aaaaaaa\U{0006}aa\U{001C}a");
}
method {:test} Test66() {
expect |"\n\0\U{0002}\U{0004}"| <= |"\U{0006}aaaaaaa\U{0008}aaaaaaa\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\n\0\U{0002}\U{0004}", "\U{0006}aaaaaaa\U{0008}aaaaaaa\U{000C}");
expect forall k :: r0 < k <= |"\n\0\U{0002}\U{0004}"| ==> !haveCommonKSubstringPred(k, "\n\0\U{0002}\U{0004}", "\U{0006}aaaaaaa\U{0008}aaaaaaa\U{000C}");
expect haveCommonKSubstringPred(r0, "\n\0\U{0002}\U{0004}", "\U{0006}aaaaaaa\U{0008}aaaaaaa\U{000C}");
}
method {:test} Test68() {
expect |"\U{0002}"| <= |"\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}", "\0");
expect forall k :: r0 < k <= |"\U{0002}"| ==> !haveCommonKSubstringPred(k, "\U{0002}", "\0");
expect haveCommonKSubstringPred(r0, "\U{0002}", "\0");
}
method {:test} Test69() {
expect |"\U{0008}aa\U{0004}\n"| <= |"\U{0006}\0aa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}aa\U{0004}\n", "\U{0006}\0aa\U{0002}");
expect forall k :: r0 < k <= |"\U{0008}aa\U{0004}\n"| ==> !haveCommonKSubstringPred(k, "\U{0008}aa\U{0004}\n", "\U{0006}\0aa\U{0002}");
expect haveCommonKSubstringPred(r0, "\U{0008}aa\U{0004}\n", "\U{0006}\0aa\U{0002}");
}

// REPEAT 5 - TIME: 38.9551715 s

method {:test} Test70() {
var r0 := isPrefix("\U{0002}\0a", "\U{0002}\0a\U{0004}aaaaaaaa");
expect !r0 <==> isNotPrefixPred("\U{0002}\0a", "\U{0002}\0a\U{0004}aaaaaaaa");
expect r0 <==> isPrefixPred("\U{0002}\0a", "\U{0002}\0a\U{0004}aaaaaaaa");
}
method {:test} Test71() {
var r0 := isPrefix("\U{0002}\U{0006}", "\U{0002}\U{0008}\0a\U{0004}");
expect !r0 <==> isNotPrefixPred("\U{0002}\U{0006}", "\U{0002}\U{0008}\0a\U{0004}");
expect r0 <==> isPrefixPred("\U{0002}\U{0006}", "\U{0002}\U{0008}\0a\U{0004}");
}
method {:test} Test72() {
var r0 := isPrefix("a\0\U{0002}aa\U{0006}aaaaaaaaaa\U{000C}\U{000E}aaaaaaa\U{0010}a", "\U{0016}aa\U{0004}aaaaa\naaa\U{0012}aaaaaaaaa\U{0008}a\U{0014}");
expect !r0 <==> isNotPrefixPred("a\0\U{0002}aa\U{0006}aaaaaaaaaa\U{000C}\U{000E}aaaaaaa\U{0010}a", "\U{0016}aa\U{0004}aaaaa\naaa\U{0012}aaaaaaaaa\U{0008}a\U{0014}");
expect r0 <==> isPrefixPred("a\0\U{0002}aa\U{0006}aaaaaaaaaa\U{000C}\U{000E}aaaaaaa\U{0010}a", "\U{0016}aa\U{0004}aaaaa\naaa\U{0012}aaaaaaaaa\U{0008}a\U{0014}");
}
method {:test} Test73() {
var r0 := isSubstring("\U{0004}\U{0002}", "\U{0006}\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0004}\U{0002}", "\U{0006}\0aaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test74() {
var r0 := isSubstring("\naaaaaa\U{0004}\U{0002}aaa\U{0006}", "\U{000C}aaaaaaaaaaa\0aa\U{0008}a\naaaaaa\U{0004}\U{0002}aaa\U{0006}");
expect r0 <==> isSubstringPred("\naaaaaa\U{0004}\U{0002}aaa\U{0006}", "\U{000C}aaaaaaaaaaa\0aa\U{0008}a\naaaaaa\U{0004}\U{0002}aaa\U{0006}");
}
method {:test} Test75() {
var r0 := isSubstring("\U{0004}aaaaaaaaaaaaaaaaaaaaaa\U{0002}a", "\U{0006}\0a");
expect r0 <==> isSubstringPred("\U{0004}aaaaaaaaaaaaaaaaaaaaaa\U{0002}a", "\U{0006}\0a");
}
method {:test} Test76() {
var r0 := haveCommonKSubstring(29, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(29, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test77() {
var r0 := haveCommonKSubstring(29, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(29, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test78() {
var r0 := haveCommonKSubstring(29, "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa", "\U{0004}\0");
expect r0 <==> haveCommonKSubstringPred(29, "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaaa", "\U{0004}\0");
}
method {:test} Test79() {
var r0 := haveCommonKSubstring(30, "aaaaaaa\na\U{0008}aaa\U{000C}aaa\U{0010}\U{0012}\U{0016}aaaa\U{000E}a\U{0014}aa", "\U{001A}aaaa\U{0002}aaaaaaaa\U{0004}aaaaaa\0\U{0006}aaaa\U{0018}");
expect r0 <==> haveCommonKSubstringPred(30, "aaaaaaa\na\U{0008}aaa\U{000C}aaa\U{0010}\U{0012}\U{0016}aaaa\U{000E}a\U{0014}aa", "\U{001A}aaaa\U{0002}aaaaaaaa\U{0004}aaaaaa\0\U{0006}aaaa\U{0018}");
}
method {:test} Test80() {
expect |"\U{0004}\U{0002}a\na\U{000C}aaaa\U{000E}\U{0010}"| <= |"aaa\0aaa\U{0008}\U{0006}aaaaaa\U{0012}a\U{0014}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}\U{0002}a\na\U{000C}aaaa\U{000E}\U{0010}", "aaa\0aaa\U{0008}\U{0006}aaaaaa\U{0012}a\U{0014}");
expect forall k :: r0 < k <= |"\U{0004}\U{0002}a\na\U{000C}aaaa\U{000E}\U{0010}"| ==> !haveCommonKSubstringPred(k, "\U{0004}\U{0002}a\na\U{000C}aaaa\U{000E}\U{0010}", "aaa\0aaa\U{0008}\U{0006}aaaaaa\U{0012}a\U{0014}");
expect haveCommonKSubstringPred(r0, "\U{0004}\U{0002}a\na\U{000C}aaaa\U{000E}\U{0010}", "aaa\0aaa\U{0008}\U{0006}aaaaaa\U{0012}a\U{0014}");
}
method {:test} Test81() {
expect |"\U{0004}\U{0002}a\U{0008}aaaaaa\n\U{000E}"| <= |"aa\0aa\U{000C}aa\U{0006}aaaaaa\U{0010}a\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}\U{0002}a\U{0008}aaaaaa\n\U{000E}", "aa\0aa\U{000C}aa\U{0006}aaaaaa\U{0010}a\U{0012}");
expect forall k :: r0 < k <= |"\U{0004}\U{0002}a\U{0008}aaaaaa\n\U{000E}"| ==> !haveCommonKSubstringPred(k, "\U{0004}\U{0002}a\U{0008}aaaaaa\n\U{000E}", "aa\0aa\U{000C}aa\U{0006}aaaaaa\U{0010}a\U{0012}");
expect haveCommonKSubstringPred(r0, "\U{0004}\U{0002}a\U{0008}aaaaaa\n\U{000E}", "aa\0aa\U{000C}aa\U{0006}aaaaaa\U{0010}a\U{0012}");
}
method {:test} Test82() {
expect |"a\U{0002}aaaa"| <= |"aaa\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("a\U{0002}aaaa", "aaa\0aa");
expect forall k :: r0 < k <= |"a\U{0002}aaaa"| ==> !haveCommonKSubstringPred(k, "a\U{0002}aaaa", "aaa\0aa");
expect haveCommonKSubstringPred(r0, "a\U{0002}aaaa", "aaa\0aa");
}
method {:test} Test83() {
expect |"\naa\U{0008}\U{0010}aa\U{0002}aa\U{0014}\U{000E}\U{0012}\U{0016}"| <= |"a\0a\U{000C}aa\U{0006}a\U{0004}aaaaaa\U{0018}\U{001C}\U{001A}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\naa\U{0008}\U{0010}aa\U{0002}aa\U{0014}\U{000E}\U{0012}\U{0016}", "a\0a\U{000C}aa\U{0006}a\U{0004}aaaaaa\U{0018}\U{001C}\U{001A}");
expect forall k :: r0 < k <= |"\naa\U{0008}\U{0010}aa\U{0002}aa\U{0014}\U{000E}\U{0012}\U{0016}"| ==> !haveCommonKSubstringPred(k, "\naa\U{0008}\U{0010}aa\U{0002}aa\U{0014}\U{000E}\U{0012}\U{0016}", "a\0a\U{000C}aa\U{0006}a\U{0004}aaaaaa\U{0018}\U{001C}\U{001A}");
expect haveCommonKSubstringPred(r0, "\naa\U{0008}\U{0010}aa\U{0002}aa\U{0014}\U{000E}\U{0012}\U{0016}", "a\0a\U{000C}aa\U{0006}a\U{0004}aaaaaa\U{0018}\U{001C}\U{001A}");
}

// REPEAT 6 - TIME: 48.8247074 s

method {:test} Test84() {
var r0 := isPrefix("\U{001C}\0a\U{0002}a\U{0008}aaaaaaa\U{0016}\U{0014}\U{0018}\U{0006}\U{0012}aaaa\U{000C}a\U{0004}\U{0010}\n\U{000E}\U{001A}", "\U{001C}\0a\U{0002}a\U{0008}aaaaaaa\U{0016}\U{0014}\U{0018}\U{0006}\U{0012}aaaa\U{000C}a\U{0004}\U{0010}\n\U{000E}\U{001A}");
expect !r0 <==> isNotPrefixPred("\U{001C}\0a\U{0002}a\U{0008}aaaaaaa\U{0016}\U{0014}\U{0018}\U{0006}\U{0012}aaaa\U{000C}a\U{0004}\U{0010}\n\U{000E}\U{001A}", "\U{001C}\0a\U{0002}a\U{0008}aaaaaaa\U{0016}\U{0014}\U{0018}\U{0006}\U{0012}aaaa\U{000C}a\U{0004}\U{0010}\n\U{000E}\U{001A}");
expect r0 <==> isPrefixPred("\U{001C}\0a\U{0002}a\U{0008}aaaaaaa\U{0016}\U{0014}\U{0018}\U{0006}\U{0012}aaaa\U{000C}a\U{0004}\U{0010}\n\U{000E}\U{001A}", "\U{001C}\0a\U{0002}a\U{0008}aaaaaaa\U{0016}\U{0014}\U{0018}\U{0006}\U{0012}aaaa\U{000C}a\U{0004}\U{0010}\n\U{000E}\U{001A}");
}
method {:test} Test85() {
var r0 := isPrefix("\U{001A}aaaa\naaaaa\U{0004}\U{000E}\U{0012}a\U{0016}a\0a\U{000C}aaa\U{0014}a\U{0010}\U{0008}\U{0018}", "\U{001A}aaaa\naaaaa\U{0004}\U{000E}\U{0012}a\U{0016}a\U{0002}a\U{000C}aaa\U{0014}a\U{0010}\U{0008}\U{0018}a\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{001A}aaaa\naaaaa\U{0004}\U{000E}\U{0012}a\U{0016}a\0a\U{000C}aaa\U{0014}a\U{0010}\U{0008}\U{0018}", "\U{001A}aaaa\naaaaa\U{0004}\U{000E}\U{0012}a\U{0016}a\U{0002}a\U{000C}aaa\U{0014}a\U{0010}\U{0008}\U{0018}a\U{0006}");
expect r0 <==> isPrefixPred("\U{001A}aaaa\naaaaa\U{0004}\U{000E}\U{0012}a\U{0016}a\0a\U{000C}aaa\U{0014}a\U{0010}\U{0008}\U{0018}", "\U{001A}aaaa\naaaaa\U{0004}\U{000E}\U{0012}a\U{0016}a\U{0002}a\U{000C}aaa\U{0014}a\U{0010}\U{0008}\U{0018}a\U{0006}");
}
method {:test} Test86() {
var r0 := isPrefix("aaa\U{0002}a\U{0008}aaaaaaa\U{0012}aaaaa\U{0010}\U{0014}aaaaaaa", "\U{001A}\0aa\U{0006}aaaa\U{000C}a\U{000E}a\naa\U{0004}aaaaaaaa\U{0016}\U{0018}");
expect !r0 <==> isNotPrefixPred("aaa\U{0002}a\U{0008}aaaaaaa\U{0012}aaaaa\U{0010}\U{0014}aaaaaaa", "\U{001A}\0aa\U{0006}aaaa\U{000C}a\U{000E}a\naa\U{0004}aaaaaaaa\U{0016}\U{0018}");
expect r0 <==> isPrefixPred("aaa\U{0002}a\U{0008}aaaaaaa\U{0012}aaaaa\U{0010}\U{0014}aaaaaaa", "\U{001A}\0aa\U{0006}aaaa\U{000C}a\U{000E}a\naa\U{0004}aaaaaaaa\U{0016}\U{0018}");
}
method {:test} Test87() {
var r0 := isSubstring("\U{0004}aa\U{0002}", "\naa\0aaaaaaaaa\U{0008}aaaa\U{0006}aaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0004}aa\U{0002}", "\naa\0aaaaaaaaa\U{0008}aaaa\U{0006}aaaaaaaaaa");
}
method {:test} Test88() {
var r0 := isSubstring("a\U{000C}a\U{0004}a\na\U{0006}", "\U{000E}aaaa\0aaaaaaa\U{0008}\U{0002}aaaaaa\U{000C}a\U{0004}a\na\U{0006}a");
expect r0 <==> isSubstringPred("a\U{000C}a\U{0004}a\na\U{0006}", "\U{000E}aaaa\0aaaaaaa\U{0008}\U{0002}aaaaaa\U{000C}a\U{0004}a\na\U{0006}a");
}
method {:test} Test89() {
var r0 := isSubstring("\U{0002}aaaa", "\0aaa");
expect r0 <==> isSubstringPred("\U{0002}aaaa", "\0aaa");
}
method {:test} Test90() {
var r0 := haveCommonKSubstring(25, "aaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(25, "aaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test91() {
var r0 := haveCommonKSubstring(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test92() {
var r0 := haveCommonKSubstring(31, "\U{0004}aaaaaaaaaaaaaaaaaaa\0aaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(31, "\U{0004}aaaaaaaaaaaaaaaaaaa\0aaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test93() {
expect |"\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}"| <= |"aaa\U{0006}\U{0004}aaaaa\0aa\U{0002}a\U{000E}a\U{0016}\U{001A}\U{0018}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}", "aaa\U{0006}\U{0004}aaaaa\0aa\U{0002}a\U{000E}a\U{0016}\U{001A}\U{0018}");
expect forall k :: r0 < k <= |"\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}"| ==> !haveCommonKSubstringPred(k, "\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}", "aaa\U{0006}\U{0004}aaaaa\0aa\U{0002}a\U{000E}a\U{0016}\U{001A}\U{0018}");
expect haveCommonKSubstringPred(r0, "\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}", "aaa\U{0006}\U{0004}aaaaa\0aa\U{0002}a\U{000E}a\U{0016}\U{001A}\U{0018}");
}
method {:test} Test94() {
expect |"\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}"| <= |"aaa\U{0006}\0aaaaa\U{0002}a\U{0004}aa\U{000E}a\U{0016}\U{0018}\U{001A}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}", "aaa\U{0006}\0aaaaa\U{0002}a\U{0004}aa\U{000E}a\U{0016}\U{0018}\U{001A}");
expect forall k :: r0 < k <= |"\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}"| ==> !haveCommonKSubstringPred(k, "\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}", "aaa\U{0006}\0aaaaa\U{0002}a\U{0004}aa\U{000E}a\U{0016}\U{0018}\U{001A}");
expect haveCommonKSubstringPred(r0, "\naaaa\U{000C}aaa\U{0008}aa\U{0010}a\U{0012}\U{0014}", "aaa\U{0006}\0aaaaa\U{0002}a\U{0004}aa\U{000E}a\U{0016}\U{0018}\U{001A}");
}
method {:test} Test95() {
expect |"\0a"| <= |"\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0a", "\U{0002}aa");
expect forall k :: r0 < k <= |"\0a"| ==> !haveCommonKSubstringPred(k, "\0a", "\U{0002}aa");
expect haveCommonKSubstringPred(r0, "\0a", "\U{0002}aa");
}
method {:test} Test96() {
expect |"\0aa"| <= |"\U{0002}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0aa", "\U{0002}aaa");
expect forall k :: r0 < k <= |"\0aa"| ==> !haveCommonKSubstringPred(k, "\0aa", "\U{0002}aaa");
expect haveCommonKSubstringPred(r0, "\0aa", "\U{0002}aaa");
}

// REPEAT 7 - TIME: 58.188219 s

method {:test} Test97() {
var r0 := isPrefix("\U{0016}aa\0a\U{0006}aaaaa\U{0008}a\U{0012}\n\U{0002}aaa\U{0010}a\U{000C}a\U{000E}a\U{0004}a", "\U{0016}aa\0a\U{0006}aaaaa\U{0008}a\U{0012}\n\U{0002}aaa\U{0010}a\U{000C}a\U{000E}a\U{0004}a\U{0014}");
expect !r0 <==> isNotPrefixPred("\U{0016}aa\0a\U{0006}aaaaa\U{0008}a\U{0012}\n\U{0002}aaa\U{0010}a\U{000C}a\U{000E}a\U{0004}a", "\U{0016}aa\0a\U{0006}aaaaa\U{0008}a\U{0012}\n\U{0002}aaa\U{0010}a\U{000C}a\U{000E}a\U{0004}a\U{0014}");
expect r0 <==> isPrefixPred("\U{0016}aa\0a\U{0006}aaaaa\U{0008}a\U{0012}\n\U{0002}aaa\U{0010}a\U{000C}a\U{000E}a\U{0004}a", "\U{0016}aa\0a\U{0006}aaaaa\U{0008}a\U{0012}\n\U{0002}aaa\U{0010}a\U{000C}a\U{000E}a\U{0004}a\U{0014}");
}
method {:test} Test98() {
var r0 := isPrefix("\U{0008}aaaaa\0aaaaa\U{0004}", "\U{0008}aaaaa\U{0002}aaaaa\U{0004}a\U{0006}aaaaaaaaaa");
expect !r0 <==> isNotPrefixPred("\U{0008}aaaaa\0aaaaa\U{0004}", "\U{0008}aaaaa\U{0002}aaaaa\U{0004}a\U{0006}aaaaaaaaaa");
expect r0 <==> isPrefixPred("\U{0008}aaaaa\0aaaaa\U{0004}", "\U{0008}aaaaa\U{0002}aaaaa\U{0004}a\U{0006}aaaaaaaaaa");
}
method {:test} Test99() {
var r0 := isPrefix("\U{0008}aa\0a\U{0004}aaaaa\U{0002}", "\U{0006}a");
expect !r0 <==> isNotPrefixPred("\U{0008}aa\0a\U{0004}aaaaa\U{0002}", "\U{0006}a");
expect r0 <==> isPrefixPred("\U{0008}aa\0a\U{0004}aaaaa\U{0002}", "\U{0006}a");
}
method {:test} Test100() {
var r0 := isSubstring("\U{0002}aaaaa", "\U{0004}aa\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0002}aaaaa", "\U{0004}aa\0aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test101() {
var r0 := isSubstring("aaaaaa", "\U{0008}aaaaaaaaa\U{0002}\0a\U{0004}aaaaaaaaa\U{0006}");
expect r0 <==> isSubstringPred("aaaaaa", "\U{0008}aaaaaaaaa\U{0002}\0a\U{0004}aaaaaaaaa\U{0006}");
}
method {:test} Test102() {
var r0 := isSubstring("aaaaaaa\U{0002}aaa\U{0004}aaaaaaaaa\U{0008}aaaaaa\U{000E}", "\U{0010}aa\0aaaaaaaaaaaaaaaaa\naaa\U{0006}a\U{000C}");
expect r0 <==> isSubstringPred("aaaaaaa\U{0002}aaa\U{0004}aaaaaaaaa\U{0008}aaaaaa\U{000E}", "\U{0010}aa\0aaaaaaaaaaaaaaaaa\naaa\U{0006}a\U{000C}");
}
method {:test} Test103() {
var r0 := haveCommonKSubstring(26, "aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(26, "aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test104() {
var r0 := haveCommonKSubstring(26, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(26, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test105() {
var r0 := haveCommonKSubstring(26, "\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(26, "\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test106() {
var r0 := haveCommonKSubstring(32, "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> haveCommonKSubstringPred(32, "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\0");
}
method {:test} Test107() {
expect |"\naaa\U{0006}\U{0002}\U{000E}aa\U{0004}a\U{0010}aa\U{0012}aa"| <= |"aaa\U{0008}\0aaaaaa\U{000C}aaaa\U{0018}\U{0016}\U{0014}a\U{001A}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\naaa\U{0006}\U{0002}\U{000E}aa\U{0004}a\U{0010}aa\U{0012}aa", "aaa\U{0008}\0aaaaaa\U{000C}aaaa\U{0018}\U{0016}\U{0014}a\U{001A}");
expect forall k :: r0 < k <= |"\naaa\U{0006}\U{0002}\U{000E}aa\U{0004}a\U{0010}aa\U{0012}aa"| ==> !haveCommonKSubstringPred(k, "\naaa\U{0006}\U{0002}\U{000E}aa\U{0004}a\U{0010}aa\U{0012}aa", "aaa\U{0008}\0aaaaaa\U{000C}aaaa\U{0018}\U{0016}\U{0014}a\U{001A}");
expect haveCommonKSubstringPred(r0, "\naaa\U{0006}\U{0002}\U{000E}aa\U{0004}a\U{0010}aa\U{0012}aa", "aaa\U{0008}\0aaaaaa\U{000C}aaaa\U{0018}\U{0016}\U{0014}a\U{001A}");
}
method {:test} Test108() {
expect |"\U{000C}aaa\U{0006}\U{0002}aaa\U{0004}aaaa\U{0014}\U{0010}\U{0012}"| <= |"aaa\U{0008}\0\U{000E}aaaaaaaaaa\n\U{0016}\U{0018}a\U{001A}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{000C}aaa\U{0006}\U{0002}aaa\U{0004}aaaa\U{0014}\U{0010}\U{0012}", "aaa\U{0008}\0\U{000E}aaaaaaaaaa\n\U{0016}\U{0018}a\U{001A}");
expect forall k :: r0 < k <= |"\U{000C}aaa\U{0006}\U{0002}aaa\U{0004}aaaa\U{0014}\U{0010}\U{0012}"| ==> !haveCommonKSubstringPred(k, "\U{000C}aaa\U{0006}\U{0002}aaa\U{0004}aaaa\U{0014}\U{0010}\U{0012}", "aaa\U{0008}\0\U{000E}aaaaaaaaaa\n\U{0016}\U{0018}a\U{001A}");
expect haveCommonKSubstringPred(r0, "\U{000C}aaa\U{0006}\U{0002}aaa\U{0004}aaaa\U{0014}\U{0010}\U{0012}", "aaa\U{0008}\0\U{000E}aaaaaaaaaa\n\U{0016}\U{0018}a\U{001A}");
}
method {:test} Test109() {
expect |"aaaaa\0aaaa\U{0006}\U{0004}aaaaa\na\U{000E}"| <= |"aaaaaaa\U{0002}aa\U{0008}aaaaa\U{000C}\U{0010}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaa\0aaaa\U{0006}\U{0004}aaaaa\na\U{000E}", "aaaaaaa\U{0002}aa\U{0008}aaaaa\U{000C}\U{0010}aaa");
expect forall k :: r0 < k <= |"aaaaa\0aaaa\U{0006}\U{0004}aaaaa\na\U{000E}"| ==> !haveCommonKSubstringPred(k, "aaaaa\0aaaa\U{0006}\U{0004}aaaaa\na\U{000E}", "aaaaaaa\U{0002}aa\U{0008}aaaaa\U{000C}\U{0010}aaa");
expect haveCommonKSubstringPred(r0, "aaaaa\0aaaa\U{0006}\U{0004}aaaaa\na\U{000E}", "aaaaaaa\U{0002}aa\U{0008}aaaaa\U{000C}\U{0010}aaa");
}
method {:test} Test110() {
expect |"\U{0002}aaaa"| <= |"\0aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aaaa", "\0aaaa");
expect forall k :: r0 < k <= |"\U{0002}aaaa"| ==> !haveCommonKSubstringPred(k, "\U{0002}aaaa", "\0aaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aaaa", "\0aaaa");
}

// REPEAT 8 - TIME: 69.3446423 s

method {:test} Test111() {
var r0 := isPrefix("\U{0010}aa\0a\U{0004}aaaaaaa\U{0008}a\na\U{0006}a\U{000C}\U{0002}aaaa\U{000E}", "\U{0010}aa\0a\U{0004}aaaaaaa\U{0008}a\na\U{0006}a\U{000C}\U{0002}aaaa\U{000E}");
expect !r0 <==> isNotPrefixPred("\U{0010}aa\0a\U{0004}aaaaaaa\U{0008}a\na\U{0006}a\U{000C}\U{0002}aaaa\U{000E}", "\U{0010}aa\0a\U{0004}aaaaaaa\U{0008}a\na\U{0006}a\U{000C}\U{0002}aaaa\U{000E}");
expect r0 <==> isPrefixPred("\U{0010}aa\0a\U{0004}aaaaaaa\U{0008}a\na\U{0006}a\U{000C}\U{0002}aaaa\U{000E}", "\U{0010}aa\0a\U{0004}aaaaaaa\U{0008}a\na\U{0006}a\U{000C}\U{0002}aaaa\U{000E}");
}
method {:test} Test112() {
var r0 := isPrefix("\U{0010}\0aaa\U{0006}aa\U{0004}aaaa\naaa\U{0008}a\U{000C}aaaaa\U{000E}", "\U{0010}\U{0002}aaa\U{0006}aa\U{0004}aaaa\naaa\U{0008}a\U{000C}aaaaa\U{000E}");
expect !r0 <==> isNotPrefixPred("\U{0010}\0aaa\U{0006}aa\U{0004}aaaa\naaa\U{0008}a\U{000C}aaaaa\U{000E}", "\U{0010}\U{0002}aaa\U{0006}aa\U{0004}aaaa\naaa\U{0008}a\U{000C}aaaaa\U{000E}");
expect r0 <==> isPrefixPred("\U{0010}\0aaa\U{0006}aa\U{0004}aaaa\naaa\U{0008}a\U{000C}aaaaa\U{000E}", "\U{0010}\U{0002}aaa\U{0006}aa\U{0004}aaaa\naaa\U{0008}a\U{000C}aaaaa\U{000E}");
}
method {:test} Test113() {
var r0 := isPrefix("\naaaa\0aaaaaaaaaaaaaaaaaaaaaaaa", "\U{0008}aaaaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaa\U{0006}");
expect !r0 <==> isNotPrefixPred("\naaaa\0aaaaaaaaaaaaaaaaaaaaaaaa", "\U{0008}aaaaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaa\U{0006}");
expect r0 <==> isPrefixPred("\naaaa\0aaaaaaaaaaaaaaaaaaaaaaaa", "\U{0008}aaaaaaaaaa\U{0002}a\U{0004}aaaaaaaaaaa\U{0006}");
}
method {:test} Test114() {
var r0 := isSubstring("\naaaaaa\U{0002}aaaaaa\U{0006}aaa\U{0004}aa", "\U{0008}aa\0aaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\naaaaaa\U{0002}aaaaaa\U{0006}aaa\U{0004}aa", "\U{0008}aa\0aaaaaaaaaaaaaaaaa");
}
method {:test} Test115() {
var r0 := isSubstring("aaaaaaa\U{0002}aa\U{0004}aaaa\U{0006}", "\U{0008}aaa\0aaaaaaa\U{0002}aa\U{0004}aaaa\U{0006}");
expect r0 <==> isSubstringPred("aaaaaaa\U{0002}aa\U{0004}aaaa\U{0006}", "\U{0008}aaa\0aaaaaaa\U{0002}aa\U{0004}aaaa\U{0006}");
}
method {:test} Test116() {
var r0 := isSubstring("aaaaaaaaaaa\U{0002}aaaaaaa\U{0008}aaaaaaaaaa", "\naa\0aaaaaaaaa\U{0006}aaaaaa\U{0004}");
expect r0 <==> isSubstringPred("aaaaaaaaaaa\U{0002}aaaaaaa\U{0008}aaaaaaaaaa", "\naa\0aaaaaaaaa\U{0006}aaaaaa\U{0004}");
}
method {:test} Test117() {
var r0 := haveCommonKSubstring(27, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(27, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test119() {
var r0 := haveCommonKSubstring(27, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(27, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test120() {
var r0 := haveCommonKSubstring(33, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(33, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test121() {
expect |"\naaaa\U{000C}aaaaa\U{0010}aa\U{0004}aaaaaa"| <= |"aaa\U{0006}\U{0008}aa\0aa\U{000E}aaaaaaaa\U{0002}\U{0012}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\naaaa\U{000C}aaaaa\U{0010}aa\U{0004}aaaaaa", "aaa\U{0006}\U{0008}aa\0aa\U{000E}aaaaaaaa\U{0002}\U{0012}a");
expect forall k :: r0 < k <= |"\naaaa\U{000C}aaaaa\U{0010}aa\U{0004}aaaaaa"| ==> !haveCommonKSubstringPred(k, "\naaaa\U{000C}aaaaa\U{0010}aa\U{0004}aaaaaa", "aaa\U{0006}\U{0008}aa\0aa\U{000E}aaaaaaaa\U{0002}\U{0012}a");
expect haveCommonKSubstringPred(r0, "\naaaa\U{000C}aaaaa\U{0010}aa\U{0004}aaaaaa", "aaa\U{0006}\U{0008}aa\0aa\U{000E}aaaaaaaa\U{0002}\U{0012}a");
}
method {:test} Test122() {
expect |"\naaaa\U{000C}aaaaaaaa\U{0004}aaaa\U{0010}a"| <= |"aaa\U{0006}\U{0008}\U{000E}a\0aaaaaaaaaaa\U{0002}\U{0012}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\naaaa\U{000C}aaaaaaaa\U{0004}aaaa\U{0010}a", "aaa\U{0006}\U{0008}\U{000E}a\0aaaaaaaaaaa\U{0002}\U{0012}a");
expect forall k :: r0 < k <= |"\naaaa\U{000C}aaaaaaaa\U{0004}aaaa\U{0010}a"| ==> !haveCommonKSubstringPred(k, "\naaaa\U{000C}aaaaaaaa\U{0004}aaaa\U{0010}a", "aaa\U{0006}\U{0008}\U{000E}a\0aaaaaaaaaaa\U{0002}\U{0012}a");
expect haveCommonKSubstringPred(r0, "\naaaa\U{000C}aaaaaaaa\U{0004}aaaa\U{0010}a", "aaa\U{0006}\U{0008}\U{000E}a\0aaaaaaaaaaa\U{0002}\U{0012}a");
}
method {:test} Test123() {
expect |"aaaaaaaaaaaaaaaaaaaaa"| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaaaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test124() {
expect |"aaaaaaaaaaaaaaaaaaaaa"| <= |"\0aaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaaaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 9 - TIME: 81.8492644 s

method {:test} Test125() {
var r0 := isPrefix("\U{0008}aaaaaaaa\0aaa\U{0004}", "\U{0008}aaaaaaaa\0aaa\U{0004}\naaaa\U{0006}a\U{0002}aa");
expect !r0 <==> isNotPrefixPred("\U{0008}aaaaaaaa\0aaa\U{0004}", "\U{0008}aaaaaaaa\0aaa\U{0004}\naaaa\U{0006}a\U{0002}aa");
expect r0 <==> isPrefixPred("\U{0008}aaaaaaaa\0aaa\U{0004}", "\U{0008}aaaaaaaa\0aaa\U{0004}\naaaa\U{0006}a\U{0002}aa");
}
method {:test} Test126() {
var r0 := isPrefix("\0\U{000E}aa\U{0002}aaaaaaaa\U{0008}", "\U{000C}aaaa\U{0004}aaaaaaa\U{0008}\U{0006}aaaa\naaaa");
expect !r0 <==> isNotPrefixPred("\0\U{000E}aa\U{0002}aaaaaaaa\U{0008}", "\U{000C}aaaa\U{0004}aaaaaaa\U{0008}\U{0006}aaaa\naaaa");
expect r0 <==> isPrefixPred("\0\U{000E}aa\U{0002}aaaaaaaa\U{0008}", "\U{000C}aaaa\U{0004}aaaaaaa\U{0008}\U{0006}aaaa\naaaa");
}
method {:test} Test127() {
var r0 := isPrefix("\U{000C}aaaaaaaaaaaa\U{0008}\na\0aaaa\U{0006}aaa", "\U{000E}aaaa\U{0002}aaaaaaa\U{0004}aaaaaaaaaa");
expect !r0 <==> isNotPrefixPred("\U{000C}aaaaaaaaaaaa\U{0008}\na\0aaaa\U{0006}aaa", "\U{000E}aaaa\U{0002}aaaaaaa\U{0004}aaaaaaaaaa");
expect r0 <==> isPrefixPred("\U{000C}aaaaaaaaaaaa\U{0008}\na\0aaaa\U{0006}aaa", "\U{000E}aaaa\U{0002}aaaaaaa\U{0004}aaaaaaaaaa");
}
method {:test} Test128() {
var r0 := isSubstring("\U{0004}aaaaaaaaaaaaaaaa\U{0002}a", "aaa\0aaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0004}aaaaaaaaaaaaaaaa\U{0002}a", "aaa\0aaaaaaaaaaaaaaaa");
}
method {:test} Test129() {
var r0 := isSubstring("\U{0002}aaa", "\0aa\U{0002}aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0002}aaa", "\0aa\U{0002}aaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test130() {
var r0 := isSubstring("\U{0006}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaa", "\U{0004}aa\0aaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0006}aaaaaaaaaaaaaaaa\U{0002}aaaaaaaaaaaa", "\U{0004}aa\0aaaaaaaaaaaaaaaa");
}
method {:test} Test131() {
var r0 := haveCommonKSubstring(23, "aaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(23, "aaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test133() {
var r0 := haveCommonKSubstring(23, "\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaa");
expect r0 <==> haveCommonKSubstringPred(23, "\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaa");
}
method {:test} Test134() {
var r0 := haveCommonKSubstring(34, "aaaaaaaaaaaaaaaaaaaaa\0a\U{0002}", "\U{0004}aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(34, "aaaaaaaaaaaaaaaaaaaaa\0a\U{0002}", "\U{0004}aaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test135() {
expect |"\U{0002}aa\0aaaaaaa\U{0006}aaaaaaa\U{0008}aa"| <= |"aaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaa\na"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aa\0aaaaaaa\U{0006}aaaaaaa\U{0008}aa", "aaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaa\na");
expect forall k :: r0 < k <= |"\U{0002}aa\0aaaaaaa\U{0006}aaaaaaa\U{0008}aa"| ==> !haveCommonKSubstringPred(k, "\U{0002}aa\0aaaaaaa\U{0006}aaaaaaa\U{0008}aa", "aaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaa\na");
expect haveCommonKSubstringPred(r0, "\U{0002}aa\0aaaaaaa\U{0006}aaaaaaa\U{0008}aa", "aaaaaaaaaa\U{0004}aaaaaaaaaaaaaaaaa\na");
}
method {:test} Test136() {
expect |"\U{0002}aa\0aaaaaaaaaaaa\U{0006}aa\U{0008}aa"| <= |"aaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaa\na"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aa\0aaaaaaaaaaaa\U{0006}aa\U{0008}aa", "aaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaa\na");
expect forall k :: r0 < k <= |"\U{0002}aa\0aaaaaaaaaaaa\U{0006}aa\U{0008}aa"| ==> !haveCommonKSubstringPred(k, "\U{0002}aa\0aaaaaaaaaaaa\U{0006}aa\U{0008}aa", "aaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaa\na");
expect haveCommonKSubstringPred(r0, "\U{0002}aa\0aaaaaaaaaaaa\U{0006}aa\U{0008}aa", "aaaaa\U{0004}aaaaaaaaaaaaaaaaaaaaaa\na");
}
method {:test} Test137() {
expect |"aaaaaaaaaaaaaa\U{0002}\0aaaa\U{0004}a"| <= |"aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaa\U{0002}\0aaaa\U{0004}a", "aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaaaaaaaaa\U{0002}\0aaaa\U{0004}a"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaaaa\U{0002}\0aaaa\U{0004}a", "aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaaaa\U{0002}\0aaaa\U{0004}a", "aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaa");
}
method {:test} Test138() {
expect |"aaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\0"| <= |"aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\0", "aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\0"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\0", "aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaa\U{0002}aaaaaaaa\U{0004}\0", "aaaaaaaaaaaaaaaaa\U{0006}aaaaaaaaaaaa");
}

// REPEAT 10 - TIME: 93.994004 s

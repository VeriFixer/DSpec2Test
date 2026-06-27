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
var r0 := isPrefix("a\0aaaaaaaaaaaaaaaaaaa", "a");
expect !r0 <==> isNotPrefixPred("a\0aaaaaaaaaaaaaaaaaaa", "a");
expect r0 <==> isPrefixPred("a\0aaaaaaaaaaaaaaaaaaa", "a");
}
method {:test} Test1() {
var r0 := isPrefix("a", "");
expect !r0 <==> isNotPrefixPred("a", "");
expect r0 <==> isPrefixPred("a", "");
}
method {:test} Test2() {
var r0 := isPrefix("aaaaaaaaaaaaaaaaaaaaa", "a");
expect !r0 <==> isNotPrefixPred("aaaaaaaaaaaaaaaaaaaaa", "a");
expect r0 <==> isPrefixPred("aaaaaaaaaaaaaaaaaaaaa", "a");
}
method {:test} Test3() {
var r0 := isPrefix("\0", "");
expect !r0 <==> isNotPrefixPred("\0", "");
expect r0 <==> isPrefixPred("\0", "");
}
method {:test} Test4() {
var r0 := isPrefix("aaaaaaaaaaaaaaaaaaa", "a");
expect !r0 <==> isNotPrefixPred("aaaaaaaaaaaaaaaaaaa", "a");
expect r0 <==> isPrefixPred("aaaaaaaaaaaaaaaaaaa", "a");
}
method {:test} Test5() {
var r0 := isPrefix("aaaaaaaaaaaaaa", "aaaaaaaaaaaaa");
expect !r0 <==> isNotPrefixPred("aaaaaaaaaaaaaa", "aaaaaaaaaaaaa");
expect r0 <==> isPrefixPred("aaaaaaaaaaaaaa", "aaaaaaaaaaaaa");
}
method {:test} Test10() {
var r0 := isPrefix("a", "a");
expect !r0 <==> isNotPrefixPred("a", "a");
expect r0 <==> isPrefixPred("a", "a");
}
method {:test} Test11() {
var r0 := isPrefix("", "a");
expect !r0 <==> isNotPrefixPred("", "a");
expect r0 <==> isPrefixPred("", "a");
}
method {:test} Test13() {
var r0 := isPrefix("aaaaaaa", "aaaaaaa");
expect !r0 <==> isNotPrefixPred("aaaaaaa", "aaaaaaa");
expect r0 <==> isPrefixPred("aaaaaaa", "aaaaaaa");
}
method {:test} Test14() {
var r0 := isPrefix("", "");
expect !r0 <==> isNotPrefixPred("", "");
expect r0 <==> isPrefixPred("", "");
}
method {:test} Test16() {
var r0 := isPrefix("a", "aa");
expect !r0 <==> isNotPrefixPred("a", "aa");
expect r0 <==> isPrefixPred("a", "aa");
}
method {:test} Test21() {
var r0 := isSubstring("a", "aaaaaaaaaaa");
expect r0 <==> isSubstringPred("a", "aaaaaaaaaaa");
}
method {:test} Test22() {
var r0 := isSubstring("", "aa");
expect r0 <==> isSubstringPred("", "aa");
}
method {:test} Test24() {
var r0 := isSubstring("aaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("aaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test25() {
var r0 := isSubstring("", "");
expect r0 <==> isSubstringPred("", "");
}
method {:test} Test26() {
var r0 := isSubstring("", "a");
expect r0 <==> isSubstringPred("", "a");
}
method {:test} Test27() {
var r0 := isSubstring("a", "aa");
expect r0 <==> isSubstringPred("a", "aa");
}
method {:test} Test28() {
var r0 := isSubstring("aaaaaa", "aaaaaaa");
expect r0 <==> isSubstringPred("aaaaaa", "aaaaaaa");
}
method {:test} Test34() {
var r0 := isSubstring("a", "");
expect r0 <==> isSubstringPred("a", "");
}
method {:test} Test35() {
var r0 := isSubstring("aa", "");
expect r0 <==> isSubstringPred("aa", "");
}
method {:test} Test43() {
var r0 := haveCommonKSubstring(6, "aaaaaaaaaaaa", "aaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(6, "aaaaaaaaaaaa", "aaaaaaaaaaaaaaaaa");
}
method {:test} Test44() {
var r0 := haveCommonKSubstring(0, "", "aa");
expect r0 <==> haveCommonKSubstringPred(0, "", "aa");
}
method {:test} Test45() {
var r0 := haveCommonKSubstring(0, "a", "aaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(0, "a", "aaaaaaaaaaa");
}
method {:test} Test46() {
var r0 := haveCommonKSubstring(7, "aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(7, "aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test47() {
var r0 := haveCommonKSubstring(0, "a", "");
expect r0 <==> haveCommonKSubstringPred(0, "a", "");
}
method {:test} Test48() {
var r0 := haveCommonKSubstring(0, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "a");
expect r0 <==> haveCommonKSubstringPred(0, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "a");
}
method {:test} Test49() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaaa", "aa");
expect r0 <==> haveCommonKSubstringPred(1, "aaaaaaaaaaaa", "aa");
}
method {:test} Test54() {
var r0 := haveCommonKSubstring(38, "", "");
expect r0 <==> haveCommonKSubstringPred(38, "", "");
}
method {:test} Test55() {
var r0 := haveCommonKSubstring(100, "", "");
expect r0 <==> haveCommonKSubstringPred(100, "", "");
}
method {:test} Test57() {
var r0 := haveCommonKSubstring(38, "a", "");
expect r0 <==> haveCommonKSubstringPred(38, "a", "");
}
method {:test} Test58() {
var r0 := haveCommonKSubstring(38, "aa", "");
expect r0 <==> haveCommonKSubstringPred(38, "aa", "");
}
method {:test} Test60() {
var r0 := haveCommonKSubstring(38, "", "a");
expect r0 <==> haveCommonKSubstringPred(38, "", "a");
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(38, "", "aa");
expect r0 <==> haveCommonKSubstringPred(38, "", "aa");
}
method {:test} Test66() {
expect |"aaaaaa"| <= |"aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaa", "aaaaaaa");
expect forall k :: r0 < k <= |"aaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaa", "aaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaa", "aaaaaaa");
}
method {:test} Test67() {
expect |""| <= |"aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("", "aa");
expect forall k :: r0 < k <= |""| ==> !haveCommonKSubstringPred(k, "", "aa");
expect haveCommonKSubstringPred(r0, "", "aa");
}
method {:test} Test68() {
expect |"a"| <= |"aaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("a", "aaaaaaaaaaa");
expect forall k :: r0 < k <= |"a"| ==> !haveCommonKSubstringPred(k, "a", "aaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "a", "aaaaaaaaaaa");
}
method {:test} Test69() {
expect |"aa"| <= |"aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aa", "aa");
expect forall k :: r0 < k <= |"aa"| ==> !haveCommonKSubstringPred(k, "aa", "aa");
expect haveCommonKSubstringPred(r0, "aa", "aa");
}
method {:test} Test70() {
expect |""| <= |""|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("", "");
expect forall k :: r0 < k <= |""| ==> !haveCommonKSubstringPred(k, "", "");
expect haveCommonKSubstringPred(r0, "", "");
}
method {:test} Test71() {
expect |"a"| <= |"a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("a", "a");
expect forall k :: r0 < k <= |"a"| ==> !haveCommonKSubstringPred(k, "a", "a");
expect haveCommonKSubstringPred(r0, "a", "a");
}
method {:test} Test74() {
expect |"aaaaaaaaaa"| <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 1 - TIME: 46.3536682 s

method {:test} Test76() {
var r0 := isPrefix("\U{0008}\naaaa\U{0004}\0", "\U{0006}\U{0002}a");
expect !r0 <==> isNotPrefixPred("\U{0008}\naaaa\U{0004}\0", "\U{0006}\U{0002}a");
expect r0 <==> isPrefixPred("\U{0008}\naaaa\U{0004}\0", "\U{0006}\U{0002}a");
}
method {:test} Test77() {
var r0 := isPrefix("\U{0004}\U{0002}aaaaa\0", "\U{0004}\U{0002}aaaaa\0");
expect !r0 <==> isNotPrefixPred("\U{0004}\U{0002}aaaaa\0", "\U{0004}\U{0002}aaaaa\0");
expect r0 <==> isPrefixPred("\U{0004}\U{0002}aaaaa\0", "\U{0004}\U{0002}aaaaa\0");
}
method {:test} Test78() {
var r0 := isSubstring("\U{0004}\U{0006}", "\U{0008}\0a\U{0002}\U{0004}\U{0006}");
expect r0 <==> isSubstringPred("\U{0004}\U{0006}", "\U{0008}\0a\U{0002}\U{0004}\U{0006}");
}
method {:test} Test79() {
var r0 := isSubstring("\U{0004}\U{0002}a", "\U{0006}\0a");
expect r0 <==> isSubstringPred("\U{0004}\U{0002}a", "\U{0006}\0a");
}
method {:test} Test80() {
var r0 := haveCommonKSubstring(8, "\U{0006}aaaaaaaa\U{0002}", "\U{0004}aaaaaaaaaa\0aaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(8, "\U{0006}aaaaaaaa\U{0002}", "\U{0004}aaaaaaaaaa\0aaaaaaaa");
}
method {:test} Test81() {
var r0 := haveCommonKSubstring(101, "\U{000C}\U{0002}aaaaaaaa\U{0006}aaaaaaaa\0", "aaaaaaaaa\U{0008}a\U{0004}aaaaa\n");
expect r0 <==> haveCommonKSubstringPred(101, "\U{000C}\U{0002}aaaaaaaa\U{0006}aaaaaaaa\0", "aaaaaaaaa\U{0008}a\U{0004}aaaaa\n");
}
method {:test} Test82() {
expect |"\U{0004}aaaaa\U{0006}"| <= |"\U{0002}aaaa\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaa\U{0006}", "\U{0002}aaaa\0aa");
expect forall k :: r0 < k <= |"\U{0004}aaaaa\U{0006}"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaa\U{0006}", "\U{0002}aaaa\0aa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaa\U{0006}", "\U{0002}aaaa\0aa");
}

// REPEAT 2 - TIME: 50.1678205 s

method {:test} Test83() {
var r0 := isPrefix("\U{0008}aa\U{0004}aa", "\U{0006}\U{0002}a\0");
expect !r0 <==> isNotPrefixPred("\U{0008}aa\U{0004}aa", "\U{0006}\U{0002}a\0");
expect r0 <==> isPrefixPred("\U{0008}aa\U{0004}aa", "\U{0006}\U{0002}a\0");
}
method {:test} Test84() {
var r0 := isPrefix("\U{0006}\U{0002}\0", "\U{0006}\U{0002}\0\U{0004}");
expect !r0 <==> isNotPrefixPred("\U{0006}\U{0002}\0", "\U{0006}\U{0002}\0\U{0004}");
expect r0 <==> isPrefixPred("\U{0006}\U{0002}\0", "\U{0006}\U{0002}\0\U{0004}");
}
method {:test} Test85() {
var r0 := isSubstring("aaaa", "\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("aaaa", "\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test86() {
var r0 := isSubstring("\U{0004}aaaaaaaaaaaaaaaaa\0\U{0008}", "\n\U{0002}a\U{0006}");
expect r0 <==> isSubstringPred("\U{0004}aaaaaaaaaaaaaaaaa\0\U{0008}", "\n\U{0002}a\U{0006}");
}
method {:test} Test87() {
var r0 := haveCommonKSubstring(9, "\U{0008}\0aaaaaaaaaaaaaaa\U{0006}aaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(9, "\U{0008}\0aaaaaaaaaaaaaaa\U{0006}aaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaa");
}
method {:test} Test88() {
var r0 := haveCommonKSubstring(102, "\U{0006}a\0", "\U{0004}\U{0002}");
expect r0 <==> haveCommonKSubstringPred(102, "\U{0006}a\0", "\U{0004}\U{0002}");
}
method {:test} Test89() {
expect |"\U{0008}\0\U{0006}aa"| <= |"\U{0004}\U{0002}aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}\0\U{0006}aa", "\U{0004}\U{0002}aaaaa");
expect forall k :: r0 < k <= |"\U{0008}\0\U{0006}aa"| ==> !haveCommonKSubstringPred(k, "\U{0008}\0\U{0006}aa", "\U{0004}\U{0002}aaaaa");
expect haveCommonKSubstringPred(r0, "\U{0008}\0\U{0006}aa", "\U{0004}\U{0002}aaaaa");
}

// REPEAT 3 - TIME: 54.5431875 s

method {:test} Test90() {
var r0 := isPrefix("\U{000C}\U{0002}aa\U{0008}a", "\U{0006}\U{0004}\0a\n");
expect !r0 <==> isNotPrefixPred("\U{000C}\U{0002}aa\U{0008}a", "\U{0006}\U{0004}\0a\n");
expect r0 <==> isPrefixPred("\U{000C}\U{0002}aa\U{0008}a", "\U{0006}\U{0004}\0a\n");
}
method {:test} Test91() {
var r0 := isPrefix("\U{0008}\U{0004}\0a", "\U{0008}\U{0004}\0a\U{0002}aa\U{0006}aa");
expect !r0 <==> isNotPrefixPred("\U{0008}\U{0004}\0a", "\U{0008}\U{0004}\0a\U{0002}aa\U{0006}aa");
expect r0 <==> isPrefixPred("\U{0008}\U{0004}\0a", "\U{0008}\U{0004}\0a\U{0002}aa\U{0006}aa");
}
method {:test} Test92() {
var r0 := isSubstring("\U{0006}\U{0002}a\naaaaaaaa\0", "\U{0004}aa\U{0008}aaaa\U{0006}\U{0002}a\naaaaaaaa\0");
expect r0 <==> isSubstringPred("\U{0006}\U{0002}a\naaaaaaaa\0", "\U{0004}aa\U{0008}aaaa\U{0006}\U{0002}a\naaaaaaaa\0");
}
method {:test} Test93() {
var r0 := isSubstring("\U{0012}\U{0002}aa\naaaaaaaaa\U{0006}a\U{000C}", "\U{0010}aa\U{0004}\0aaaaa\U{0008}aa\U{000E}aaaaa");
expect r0 <==> isSubstringPred("\U{0012}\U{0002}aa\naaaaaaaaa\U{0006}a\U{000C}", "\U{0010}aa\U{0004}\0aaaaa\U{0008}aa\U{000E}aaaaa");
}
method {:test} Test94() {
var r0 := haveCommonKSubstring(11, "\U{0008}aaa\U{0002}aaaaa\naaaaaaaaaaa", "\U{0006}aaa\0aaa\U{0004}aa\U{000C}aaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(11, "\U{0008}aaa\U{0002}aaaaa\naaaaaaaaaaa", "\U{0006}aaa\0aaa\U{0004}aa\U{000C}aaaaaaaaaaaaaaaaaa");
}
method {:test} Test95() {
var r0 := haveCommonKSubstring(103, "\U{0004}a\0aaaaaaaaaa", "\U{0006}\U{0002}a");
expect r0 <==> haveCommonKSubstringPred(103, "\U{0004}a\0aaaaaaaaaa", "\U{0006}\U{0002}a");
}
method {:test} Test96() {
expect |"\U{0002}aaaa\U{0004}\U{0006}a"| <= |"\U{0008}\0aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aaaa\U{0004}\U{0006}a", "\U{0008}\0aaaaaaa");
expect forall k :: r0 < k <= |"\U{0002}aaaa\U{0004}\U{0006}a"| ==> !haveCommonKSubstringPred(k, "\U{0002}aaaa\U{0004}\U{0006}a", "\U{0008}\0aaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aaaa\U{0004}\U{0006}a", "\U{0008}\0aaaaaaa");
}

// REPEAT 4 - TIME: 58.9346742 s

method {:test} Test97() {
var r0 := isPrefix("\U{000C}aaa\U{0006}a\0\U{0008}a", "\n\U{0002}aa\U{0004}a");
expect !r0 <==> isNotPrefixPred("\U{000C}aaa\U{0006}a\0\U{0008}a", "\n\U{0002}aa\U{0004}a");
expect r0 <==> isPrefixPred("\U{000C}aaa\U{0006}a\0\U{0008}a", "\n\U{0002}aa\U{0004}a");
}
method {:test} Test98() {
var r0 := isPrefix("\U{0004}\0", "\U{0004}\0\U{0002}");
expect !r0 <==> isNotPrefixPred("\U{0004}\0", "\U{0004}\0\U{0002}");
expect r0 <==> isPrefixPred("\U{0004}\0", "\U{0004}\0\U{0002}");
}
method {:test} Test99() {
var r0 := isSubstring("\U{000C}\U{0002}\0aaa\U{0006}", "\naaa\U{0008}a\U{0004}\U{000C}\U{0002}\0aaa\U{0006}");
expect r0 <==> isSubstringPred("\U{000C}\U{0002}\0aaa\U{0006}", "\naaa\U{0008}a\U{0004}\U{000C}\U{0002}\0aaa\U{0006}");
}
method {:test} Test100() {
var r0 := isSubstring("\U{000E}\U{0002}aa\U{0004}a\U{0008}", "\U{000C}\0aaaaaaa\U{0006}a\n");
expect r0 <==> isSubstringPred("\U{000E}\U{0002}aa\U{0004}a\U{0008}", "\U{000C}\0aaaaaaa\U{0006}a\n");
}
method {:test} Test101() {
var r0 := haveCommonKSubstring(12, "a\0aaa\U{0006}aaaaaaaaaaaaaaa\U{000C}\U{000E}", "aaaaa\U{0004}aaaaa\U{0008}\U{0002}aaaaaaaaaaaaaaa\n");
expect r0 <==> haveCommonKSubstringPred(12, "a\0aaa\U{0006}aaaaaaaaaaaaaaa\U{000C}\U{000E}", "aaaaa\U{0004}aaaaa\U{0008}\U{0002}aaaaaaaaaaaaaaa\n");
}
method {:test} Test102() {
var r0 := haveCommonKSubstring(104, "\U{0004}\U{0002}a", "\U{0006}aaaaaaaaaa\0");
expect r0 <==> haveCommonKSubstringPred(104, "\U{0004}\U{0002}a", "\U{0006}aaaaaaaaaa\0");
}
method {:test} Test103() {
expect |"\naaaaaaa\U{0006}\U{0008}"| <= |"\0aaaaaa\U{0002}a\U{0004}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\naaaaaaa\U{0006}\U{0008}", "\0aaaaaa\U{0002}a\U{0004}aaa");
expect forall k :: r0 < k <= |"\naaaaaaa\U{0006}\U{0008}"| ==> !haveCommonKSubstringPred(k, "\naaaaaaa\U{0006}\U{0008}", "\0aaaaaa\U{0002}a\U{0004}aaa");
expect haveCommonKSubstringPred(r0, "\naaaaaaa\U{0006}\U{0008}", "\0aaaaaa\U{0002}a\U{0004}aaa");
}

// REPEAT 5 - TIME: 63.6863626 s

method {:test} Test104() {
var r0 := isPrefix("\U{0008}aa\U{0004}a\0", "\n\U{0002}a\U{0006}a");
expect !r0 <==> isNotPrefixPred("\U{0008}aa\U{0004}a\0", "\n\U{0002}a\U{0006}a");
expect r0 <==> isPrefixPred("\U{0008}aa\U{0004}a\0", "\n\U{0002}a\U{0006}a");
}
method {:test} Test105() {
var r0 := isPrefix("\U{0006}\0aa\U{0004}\U{0002}a", "\U{0006}\0aa\U{0004}\U{0002}a");
expect !r0 <==> isNotPrefixPred("\U{0006}\0aa\U{0004}\U{0002}a", "\U{0006}\0aa\U{0004}\U{0002}a");
expect r0 <==> isPrefixPred("\U{0006}\0aa\U{0004}\U{0002}a", "\U{0006}\0aa\U{0004}\U{0002}a");
}
method {:test} Test106() {
var r0 := isSubstring("\n\U{000E}\0\U{0002}\U{0006}", "\U{000C}\U{0004}\U{0008}a\n\U{000E}\0\U{0002}\U{0006}aaaa");
expect r0 <==> isSubstringPred("\n\U{000E}\0\U{0002}\U{0006}", "\U{000C}\U{0004}\U{0008}a\n\U{000E}\0\U{0002}\U{0006}aaaa");
}
method {:test} Test107() {
var r0 := isSubstring("\U{000E}a\U{0002}\U{0004}aa\U{0008}a", "\0aaaaaaa\U{0006}aa\na\U{000C}aaaaaaaa");
expect r0 <==> isSubstringPred("\U{000E}a\U{0002}\U{0004}aa\U{0008}a", "\0aaaaaaa\U{0006}aa\na\U{000C}aaaaaaaa");
}
method {:test} Test108() {
var r0 := haveCommonKSubstring(13, "\U{000E}\U{0002}a\U{0008}aaaaaaaaaaaaaa\n", "\U{000C}\0a\U{0006}\U{0004}aaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(13, "\U{000E}\U{0002}a\U{0008}aaaaaaaaaaaaaa\n", "\U{000C}\0a\U{0006}\U{0004}aaaaaaaaaaaaaa");
}
method {:test} Test109() {
var r0 := haveCommonKSubstring(105, "\U{000E}\U{0004}aaaaaaaaa\U{000C}a\0", "\U{0008}\U{0002}\U{0006}\n");
expect r0 <==> haveCommonKSubstringPred(105, "\U{000E}\U{0004}aaaaaaaaa\U{000C}a\0", "\U{0008}\U{0002}\U{0006}\n");
}
method {:test} Test110() {
expect |"\U{0008}aa\0"| <= |"\U{0004}aa\U{0002}aaa\U{0006}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}aa\0", "\U{0004}aa\U{0002}aaa\U{0006}aaa");
expect forall k :: r0 < k <= |"\U{0008}aa\0"| ==> !haveCommonKSubstringPred(k, "\U{0008}aa\0", "\U{0004}aa\U{0002}aaa\U{0006}aaa");
expect haveCommonKSubstringPred(r0, "\U{0008}aa\0", "\U{0004}aa\U{0002}aaa\U{0006}aaa");
}

// REPEAT 6 - TIME: 68.5363449 s

method {:test} Test111() {
var r0 := isPrefix("\U{000E}aaaa\U{0008}aaa\U{001E}\U{0012}aa\U{0018}\U{0006}aa\U{0002}\U{001C} ", "\U{000C}\U{0004}aa\na\U{0010}\U{0016}aaaa\U{001A}aaa\U{0014}a\0");
expect !r0 <==> isNotPrefixPred("\U{000E}aaaa\U{0008}aaa\U{001E}\U{0012}aa\U{0018}\U{0006}aa\U{0002}\U{001C} ", "\U{000C}\U{0004}aa\na\U{0010}\U{0016}aaaa\U{001A}aaa\U{0014}a\0");
expect r0 <==> isPrefixPred("\U{000E}aaaa\U{0008}aaa\U{001E}\U{0012}aa\U{0018}\U{0006}aa\U{0002}\U{001C} ", "\U{000C}\U{0004}aa\na\U{0010}\U{0016}aaaa\U{001A}aaa\U{0014}a\0");
}
method {:test} Test112() {
var r0 := isPrefix("\U{0012}\U{0002}\U{0004}a\0\U{0008}a\U{000C}a\U{000E}a\na", "\U{0012}\U{0002}\U{0004}a\0\U{0008}a\U{000C}a\U{000E}a\naa\U{0010}\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{0012}\U{0002}\U{0004}a\0\U{0008}a\U{000C}a\U{000E}a\na", "\U{0012}\U{0002}\U{0004}a\0\U{0008}a\U{000C}a\U{000E}a\naa\U{0010}\U{0006}");
expect r0 <==> isPrefixPred("\U{0012}\U{0002}\U{0004}a\0\U{0008}a\U{000C}a\U{000E}a\na", "\U{0012}\U{0002}\U{0004}a\0\U{0008}a\U{000C}a\U{000E}a\naa\U{0010}\U{0006}");
}
method {:test} Test113() {
var r0 := isSubstring("\U{0002}\U{0004}", "\0aaa\U{0002}\U{0004}");
expect r0 <==> isSubstringPred("\U{0002}\U{0004}", "\0aaa\U{0002}\U{0004}");
}
method {:test} Test114() {
var r0 := isSubstring("\U{0018}aaaaaa\U{000E}\U{0006}aa\U{0008}a\U{0014}a\U{0010}a\0", "\U{0016}\U{0004}aaaaaaaa\U{0002}\U{0012}a\naaa\U{000C}aa");
expect r0 <==> isSubstringPred("\U{0018}aaaaaa\U{000E}\U{0006}aa\U{0008}a\U{0014}a\U{0010}a\0", "\U{0016}\U{0004}aaaaaaaa\U{0002}\U{0012}a\naaa\U{000C}aa");
}
method {:test} Test115() {
var r0 := haveCommonKSubstring(14, "\U{000E}\0a\naaaaaaaaaaaaaaaa\U{000C}", "\U{0004}aaaaaa\U{0006}\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(14, "\U{000E}\0a\naaaaaaaaaaaaaaaa\U{000C}", "\U{0004}aaaaaa\U{0006}\U{0008}aa\U{0002}aaaaaaaaaaaaaaaaa");
}
method {:test} Test116() {
var r0 := haveCommonKSubstring(106, "\n\U{0004}aaaaaaaaaaaaaaaaaa\0", "\U{0008}\U{0002}\U{0006}");
expect r0 <==> haveCommonKSubstringPred(106, "\n\U{0004}aaaaaaaaaaaaaaaaaa\0", "\U{0008}\U{0002}\U{0006}");
}
method {:test} Test117() {
expect |"\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0"| <= |"\U{0004}aaaaa\U{0002}aa\U{0010}aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0", "\U{0004}aaaaa\U{0002}aa\U{0010}aaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0"| ==> !haveCommonKSubstringPred(k, "\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0", "\U{0004}aaaaa\U{0002}aa\U{0010}aaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0", "\U{0004}aaaaa\U{0002}aa\U{0010}aaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 7 - TIME: 74.2494595 s

method {:test} Test118() {
var r0 := isPrefix("\U{0014}aa\U{0004}a\U{0002}aa\U{000E}\U{0010}a", "\U{0012}\0aaa\U{000C}\n\U{0006}\U{0008}a");
expect !r0 <==> isNotPrefixPred("\U{0014}aa\U{0004}a\U{0002}aa\U{000E}\U{0010}a", "\U{0012}\0aaa\U{000C}\n\U{0006}\U{0008}a");
expect r0 <==> isPrefixPred("\U{0014}aa\U{0004}a\U{0002}aa\U{000E}\U{0010}a", "\U{0012}\0aaa\U{000C}\n\U{0006}\U{0008}a");
}
method {:test} Test119() {
var r0 := isPrefix("a\U{0002}aaa\U{000C}\U{0004}\U{0010}a\U{0014}a\U{000E}a\n\U{0016}\U{0018}\0\U{0006}\U{0008}\U{001A}\U{001C} \U{001E}aa\U{0012}aa", "a\U{0002}aaa\U{000C}\U{0004}\U{0010}a\U{0014}a\U{000E}a\n\U{0016}\U{0018}\0\U{0006}\U{0008}\U{001A}\U{001C} \U{001E}aa\U{0012}aa");
expect !r0 <==> isNotPrefixPred("a\U{0002}aaa\U{000C}\U{0004}\U{0010}a\U{0014}a\U{000E}a\n\U{0016}\U{0018}\0\U{0006}\U{0008}\U{001A}\U{001C} \U{001E}aa\U{0012}aa", "a\U{0002}aaa\U{000C}\U{0004}\U{0010}a\U{0014}a\U{000E}a\n\U{0016}\U{0018}\0\U{0006}\U{0008}\U{001A}\U{001C} \U{001E}aa\U{0012}aa");
expect r0 <==> isPrefixPred("a\U{0002}aaa\U{000C}\U{0004}\U{0010}a\U{0014}a\U{000E}a\n\U{0016}\U{0018}\0\U{0006}\U{0008}\U{001A}\U{001C} \U{001E}aa\U{0012}aa", "a\U{0002}aaa\U{000C}\U{0004}\U{0010}a\U{0014}a\U{000E}a\n\U{0016}\U{0018}\0\U{0006}\U{0008}\U{001A}\U{001C} \U{001E}aa\U{0012}aa");
}
method {:test} Test120() {
var r0 := isSubstring("\U{0002}a\0", "\U{0004}a\U{0002}a\0");
expect r0 <==> isSubstringPred("\U{0002}a\0", "\U{0004}a\U{0002}a\0");
}
method {:test} Test121() {
var r0 := isSubstring("\U{0010}\0aa\n\U{000E}\U{0008}", "\U{0012}aaaaaaaa\U{000C}\U{0006}aaaa\U{0002}aaa\U{0004}a");
expect r0 <==> isSubstringPred("\U{0010}\0aa\n\U{000E}\U{0008}", "\U{0012}aaaaaaaa\U{000C}\U{0006}aaaa\U{0002}aaa\U{0004}a");
}
method {:test} Test122() {
var r0 := haveCommonKSubstring(15, "\U{0010}a\U{0006}aaaaaaaaaaaaaaaaa\U{000C}aa", "\U{0004}\U{0002}aaa\na\U{0008}a\0aa\U{000E}aaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(15, "\U{0010}a\U{0006}aaaaaaaaaaaaaaaaa\U{000C}aa", "\U{0004}\U{0002}aaa\na\U{0008}a\0aa\U{000E}aaaaaaaaaaaaaaa");
}
method {:test} Test123() {
var r0 := haveCommonKSubstring(107, "\U{000C}aaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaaa\0", "\U{0004}aaaaaaaaaa\na\U{0006}a\U{0002}aa");
expect r0 <==> haveCommonKSubstringPred(107, "\U{000C}aaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaaa\0", "\U{0004}aaaaaaaaaa\na\U{0006}a\U{0002}aa");
}
method {:test} Test124() {
expect |"\U{0004}aa\0"| <= |"\U{0002}aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aa\0", "\U{0002}aaaa");
expect forall k :: r0 < k <= |"\U{0004}aa\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}aa\0", "\U{0002}aaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aa\0", "\U{0002}aaaa");
}

// REPEAT 8 - TIME: 80.1949343 s

method {:test} Test125() {
var r0 := isPrefix("\U{0008}aaa\U{0002}aaaaaaaa", "\n\0a\U{0004}a\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{0008}aaa\U{0002}aaaaaaaa", "\n\0a\U{0004}a\U{0006}");
expect r0 <==> isPrefixPred("\U{0008}aaa\U{0002}aaaaaaaa", "\n\0a\U{0004}a\U{0006}");
}
method {:test} Test126() {
var r0 := isPrefix("\U{0002}\0", "\U{0002}\0");
expect !r0 <==> isNotPrefixPred("\U{0002}\0", "\U{0002}\0");
expect r0 <==> isPrefixPred("\U{0002}\0", "\U{0002}\0");
}
method {:test} Test127() {
var r0 := isSubstring("\"\U{0002}\0\U{0004}\U{0008}a\U{0006}\U{0010}\U{0012}\U{0014}a\U{0016}", " aaa\n\U{000C}\U{000E}aaaa\U{0018}\U{001A}\U{001C}a\U{001E}a\"\U{0002}\0\U{0004}\U{0008}a\U{0006}\U{0010}\U{0012}\U{0014}a\U{0016}");
expect r0 <==> isSubstringPred("\"\U{0002}\0\U{0004}\U{0008}a\U{0006}\U{0010}\U{0012}\U{0014}a\U{0016}", " aaa\n\U{000C}\U{000E}aaaa\U{0018}\U{001A}\U{001C}a\U{001E}a\"\U{0002}\0\U{0004}\U{0008}a\U{0006}\U{0010}\U{0012}\U{0014}a\U{0016}");
}
method {:test} Test128() {
var r0 := isSubstring("aaa\0a\naaaaa\U{0006}aaaaa\U{0014}aaa\U{000E}aa\U{0018}", "\U{0004}\U{0002}aaaaaaa\U{0008}a\U{000C}a\U{0012}aaaa\U{0010}\U{0016}a\U{001A}\U{001C}");
expect r0 <==> isSubstringPred("aaa\0a\naaaaa\U{0006}aaaaa\U{0014}aaa\U{000E}aa\U{0018}", "\U{0004}\U{0002}aaaaaaa\U{0008}a\U{000C}a\U{0012}aaaa\U{0010}\U{0016}a\U{001A}\U{001C}");
}
method {:test} Test129() {
var r0 := haveCommonKSubstring(16, "\n\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\0aaaaaaaaa\U{0006}aaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(16, "\n\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\0aaaaaaaaa\U{0006}aaaaaaaaaaaaaaaa");
}
method {:test} Test130() {
var r0 := haveCommonKSubstring(108, "\U{0006}\U{0002}", "\U{0004}a\0aa");
expect r0 <==> haveCommonKSubstringPred(108, "\U{0006}\U{0002}", "\U{0004}a\0aa");
}
method {:test} Test131() {
expect |"\U{0008}aaa\0a\U{0002}"| <= |"\naaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}aaa\0a\U{0002}", "\naaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0008}aaa\0a\U{0002}"| ==> !haveCommonKSubstringPred(k, "\U{0008}aaa\0a\U{0002}", "\naaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0008}aaa\0a\U{0002}", "\naaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 9 - TIME: 86.3622361 s

method {:test} Test132() {
var r0 := isPrefix("\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaa\0a");
expect !r0 <==> isNotPrefixPred("\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaa\0a");
expect r0 <==> isPrefixPred("\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaa\0a");
}
method {:test} Test133() {
var r0 := isPrefix("\U{000E}\0a\U{0010}a\U{0002}a\U{0004}\U{0006}\U{000C}", "\U{000E}\0a\U{0010}a\U{0002}a\U{0004}\U{0006}\U{000C}\n\U{0008}aa");
expect !r0 <==> isNotPrefixPred("\U{000E}\0a\U{0010}a\U{0002}a\U{0004}\U{0006}\U{000C}", "\U{000E}\0a\U{0010}a\U{0002}a\U{0004}\U{0006}\U{000C}\n\U{0008}aa");
expect r0 <==> isPrefixPred("\U{000E}\0a\U{0010}a\U{0002}a\U{0004}\U{0006}\U{000C}", "\U{000E}\0a\U{0010}a\U{0002}a\U{0004}\U{0006}\U{000C}\n\U{0008}aa");
}
method {:test} Test134() {
var r0 := isSubstring("\U{0010}aaa\U{0008}a\U{000C}\0\U{0002}a\U{0004}aa", "\U{000E}aaaa\U{0006}\naaa\U{0010}aaa\U{0008}a\U{000C}\0\U{0002}a\U{0004}aaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0010}aaa\U{0008}a\U{000C}\0\U{0002}a\U{0004}aa", "\U{000E}aaaa\U{0006}\naaa\U{0010}aaa\U{0008}a\U{000C}\0\U{0002}a\U{0004}aaaaaaaaa");
}
method {:test} Test135() {
var r0 := isSubstring("a\U{0002}aaaaaaaaaaa\U{0010}a\U{0008}a\U{0016}aa\U{001A}aa\U{0018}\0\U{000C}", " aaaaaaaaaa\U{000E}aaa\U{0004}aaa\U{0014}a\U{001C}a\U{001E}\U{0006}\U{0012}aa\na");
expect r0 <==> isSubstringPred("a\U{0002}aaaaaaaaaaa\U{0010}a\U{0008}a\U{0016}aa\U{001A}aa\U{0018}\0\U{000C}", " aaaaaaaaaa\U{000E}aaa\U{0004}aaa\U{0014}a\U{001C}a\U{001E}\U{0006}\U{0012}aa\na");
}
method {:test} Test136() {
var r0 := haveCommonKSubstring(18, "\U{0014}\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaa\U{0010}a\U{0008}\U{0012}", "\0\U{0004}aaaaaaaaaaaaaaaa\U{000C}a\n\U{000E}");
expect r0 <==> haveCommonKSubstringPred(18, "\U{0014}\U{0002}\U{0006}aaaaaaaaaaaaaaaaaaaaa\U{0010}a\U{0008}\U{0012}", "\0\U{0004}aaaaaaaaaaaaaaaa\U{000C}a\n\U{000E}");
}
method {:test} Test137() {
var r0 := haveCommonKSubstring(109, "\U{0006}aaaaaaaaaaaa\0", "\U{0004}\U{0002}aa");
expect r0 <==> haveCommonKSubstringPred(109, "\U{0006}aaaaaaaaaaaa\0", "\U{0004}\U{0002}aa");
}
method {:test} Test138() {
expect |"\U{0004}a\0a"| <= |"\U{0002}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}a\0a", "\U{0002}aaa");
expect forall k :: r0 < k <= |"\U{0004}a\0a"| ==> !haveCommonKSubstringPred(k, "\U{0004}a\0a", "\U{0002}aaa");
expect haveCommonKSubstringPred(r0, "\U{0004}a\0a", "\U{0002}aaa");
}

// REPEAT 10 - TIME: 92.5297855 s

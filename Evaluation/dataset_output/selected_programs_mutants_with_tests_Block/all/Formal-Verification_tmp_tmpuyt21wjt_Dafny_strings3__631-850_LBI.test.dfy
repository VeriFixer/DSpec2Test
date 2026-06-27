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

// REPEAT 1 - TIME: 9.4294676 s

method {:test} Test14() {
var r0 := isPrefix("aaaaa\U{0002}", "aaaaa\U{0002}\0");
expect !r0 <==> isNotPrefixPred("aaaaa\U{0002}", "aaaaa\U{0002}\0");
expect r0 <==> isPrefixPred("aaaaa\U{0002}", "aaaaa\U{0002}\0");
}
method {:test} Test15() {
var r0 := isPrefix("\0\U{0002}\U{0004}aa\U{0006}", "\U{0008}\U{0002}aaa\U{0006}");
expect !r0 <==> isNotPrefixPred("\0\U{0002}\U{0004}aa\U{0006}", "\U{0008}\U{0002}aaa\U{0006}");
expect r0 <==> isPrefixPred("\0\U{0002}\U{0004}aa\U{0006}", "\U{0008}\U{0002}aaa\U{0006}");
}
method {:test} Test16() {
var r0 := isPrefix("aa\U{0002}", "\U{0004}\0");
expect !r0 <==> isNotPrefixPred("aa\U{0002}", "\U{0004}\0");
expect r0 <==> isPrefixPred("aa\U{0002}", "\U{0004}\0");
}
method {:test} Test17() {
var r0 := isSubstring("aa\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaa\U{0006}", "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("aa\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaa\U{0006}", "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test18() {
var r0 := isSubstring("aaa\U{0004}aaaaaaaaaaaaaaa\U{0002}", "a\0aaa\U{0004}aaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> isSubstringPred("aaa\U{0004}aaaaaaaaaaaaaaa\U{0002}", "a\0aaa\U{0004}aaaaaaaaaaaaaaa\U{0002}");
}
method {:test} Test19() {
var r0 := isSubstring("\U{0004}\U{0002}a", "a\0");
expect r0 <==> isSubstringPred("\U{0004}\U{0002}a", "a\0");
}
method {:test} Test20() {
var r0 := haveCommonKSubstring(3, "\U{0004}a\U{0002}", "a\0aa");
expect r0 <==> haveCommonKSubstringPred(3, "\U{0004}a\U{0002}", "a\0aa");
}
method {:test} Test21() {
var r0 := haveCommonKSubstring(10, "aaaaaaaaaaaa", "aaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(10, "aaaaaaaaaaaa", "aaaaaaaaaaa");
}
method {:test} Test22() {
var r0 := haveCommonKSubstring(5, "aaaaa", "aaa\0");
expect r0 <==> haveCommonKSubstringPred(5, "aaaaa", "aaa\0");
}
method {:test} Test23() {
var r0 := haveCommonKSubstring(13, "\U{0004}\U{0002}aaaaaaaaaa", "a\0");
expect r0 <==> haveCommonKSubstringPred(13, "\U{0004}\U{0002}aaaaaaaaaa", "a\0");
}
method {:test} Test24() {
expect |"\U{0002}a"| <= |"\U{0004}\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}a", "\U{0004}\0");
expect forall k :: r0 < k <= |"\U{0002}a"| ==> !haveCommonKSubstringPred(k, "\U{0002}a", "\U{0004}\0");
expect haveCommonKSubstringPred(r0, "\U{0002}a", "\U{0004}\0");
}
method {:test} Test26() {
expect |"aa"| <= |"\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aa", "\0a");
expect forall k :: r0 < k <= |"aa"| ==> !haveCommonKSubstringPred(k, "aa", "\0a");
expect haveCommonKSubstringPred(r0, "aa", "\0a");
}
method {:test} Test27() {
expect |"aaaaaaaaaaaa\0"| <= |"aaaaaaaaaaaaaaa\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaa\0", "aaaaaaaaaaaaaaa\U{0002}");
expect forall k :: r0 < k <= |"aaaaaaaaaaaa\0"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaa\0", "aaaaaaaaaaaaaaa\U{0002}");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaa\0", "aaaaaaaaaaaaaaa\U{0002}");
}

// REPEAT 2 - TIME: 15.3595593 s

method {:test} Test28() {
var r0 := isPrefix("\0aaa\U{0002}", "\0aaa\U{0002}");
expect !r0 <==> isNotPrefixPred("\0aaa\U{0002}", "\0aaa\U{0002}");
expect r0 <==> isPrefixPred("\0aaa\U{0002}", "\0aaa\U{0002}");
}
method {:test} Test29() {
var r0 := isPrefix("\U{0004}\U{0002}aa\U{0008}", "\U{0006}\0aaa");
expect !r0 <==> isNotPrefixPred("\U{0004}\U{0002}aa\U{0008}", "\U{0006}\0aaa");
expect r0 <==> isPrefixPred("\U{0004}\U{0002}aa\U{0008}", "\U{0006}\0aaa");
}
method {:test} Test30() {
var r0 := isPrefix("\U{0004}\0aa", "\U{0002}a");
expect !r0 <==> isNotPrefixPred("\U{0004}\0aa", "\U{0002}a");
expect r0 <==> isPrefixPred("\U{0004}\0aa", "\U{0002}a");
}
method {:test} Test31() {
var r0 := isSubstring("\U{0004}\0aaaaaaaaaaaaaaaaaaaaa\U{0006}\n", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aa");
expect r0 <==> isSubstringPred("\U{0004}\0aaaaaaaaaaaaaaaaaaaaa\U{0006}\n", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aa");
}
method {:test} Test32() {
var r0 := isSubstring("\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaa\U{0006}", "\na\0aa\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaa\U{0006}");
expect r0 <==> isSubstringPred("\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaa\U{0006}", "\na\0aa\U{0008}aaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaa\U{0006}");
}
method {:test} Test33() {
var r0 := isSubstring("\U{0004}\0a\U{0002}", "\U{0006}aa");
expect r0 <==> isSubstringPred("\U{0004}\0a\U{0002}", "\U{0006}aa");
}
method {:test} Test34() {
var r0 := haveCommonKSubstring(14, "aaaaaaa\U{0002}aaaaa\n", "\U{0004}\0a\U{0006}aaaaa\U{0008}aaaa");
expect r0 <==> haveCommonKSubstringPred(14, "aaaaaaa\U{0002}aaaaa\n", "\U{0004}\0a\U{0006}aaaaa\U{0008}aaaa");
}
method {:test} Test35() {
var r0 := haveCommonKSubstring(14, "aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(14, "aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test36() {
var r0 := haveCommonKSubstring(14, "\U{000C}aa\U{0004}a\U{0008}aaaaaaaa", "\n\0a\U{0002}aaaaaaa\U{0006}");
expect r0 <==> haveCommonKSubstringPred(14, "\U{000C}aa\U{0004}a\U{0008}aaaaaaaa", "\n\0a\U{0002}aaaaaaa\U{0006}");
}
method {:test} Test37() {
var r0 := haveCommonKSubstring(14, "\na\U{0004}\U{0006}", "\U{0008}\U{0002}\0");
expect r0 <==> haveCommonKSubstringPred(14, "\na\U{0004}\U{0006}", "\U{0008}\U{0002}\0");
}
method {:test} Test38() {
expect |"\U{0002}a"| <= |"\U{0004}\0a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}a", "\U{0004}\0a");
expect forall k :: r0 < k <= |"\U{0002}a"| ==> !haveCommonKSubstringPred(k, "\U{0002}a", "\U{0004}\0a");
expect haveCommonKSubstringPred(r0, "\U{0002}a", "\U{0004}\0a");
}
method {:test} Test40() {
expect |"\U{0008}\U{0002}aaaaaaaa\n"| <= |"\U{000C}\0aa\U{0006}aaaa\U{0004}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}\U{0002}aaaaaaaa\n", "\U{000C}\0aa\U{0006}aaaa\U{0004}a");
expect forall k :: r0 < k <= |"\U{0008}\U{0002}aaaaaaaa\n"| ==> !haveCommonKSubstringPred(k, "\U{0008}\U{0002}aaaaaaaa\n", "\U{000C}\0aa\U{0006}aaaa\U{0004}a");
expect haveCommonKSubstringPred(r0, "\U{0008}\U{0002}aaaaaaaa\n", "\U{000C}\0aa\U{0006}aaaa\U{0004}a");
}
method {:test} Test41() {
expect |"\U{0002}aa"| <= |"\U{0004}a\0"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aa", "\U{0004}a\0");
expect forall k :: r0 < k <= |"\U{0002}aa"| ==> !haveCommonKSubstringPred(k, "\U{0002}aa", "\U{0004}a\0");
expect haveCommonKSubstringPred(r0, "\U{0002}aa", "\U{0004}a\0");
}

// REPEAT 3 - TIME: 21.2467683 s

method {:test} Test42() {
var r0 := isPrefix("\U{0002}\U{0004}\0a\U{0006}", "\U{0002}\U{0004}\0a\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{0002}\U{0004}\0a\U{0006}", "\U{0002}\U{0004}\0a\U{0006}");
expect r0 <==> isPrefixPred("\U{0002}\U{0004}\0a\U{0006}", "\U{0002}\U{0004}\0a\U{0006}");
}
method {:test} Test43() {
var r0 := isPrefix("\U{0006}\U{0008}\0", "\U{0006}\U{0008}\U{0002}aa\U{0004}");
expect !r0 <==> isNotPrefixPred("\U{0006}\U{0008}\0", "\U{0006}\U{0008}\U{0002}aa\U{0004}");
expect r0 <==> isPrefixPred("\U{0006}\U{0008}\0", "\U{0006}\U{0008}\U{0002}aa\U{0004}");
}
method {:test} Test44() {
var r0 := isPrefix("\U{0004}aa\U{0002}", "\0a");
expect !r0 <==> isNotPrefixPred("\U{0004}aa\U{0002}", "\0a");
expect r0 <==> isPrefixPred("\U{0004}aa\U{0002}", "\0a");
}
method {:test} Test45() {
var r0 := isSubstring("aaaaaaaaaaaaaaaaaa\U{0004}aaaaaa\n\U{0006}\U{000C}", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0008}aa");
expect r0 <==> isSubstringPred("aaaaaaaaaaaaaaaaaa\U{0004}aaaaaa\n\U{0006}\U{000C}", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaa\U{0008}aa");
}
method {:test} Test46() {
var r0 := isSubstring("\U{000C}aaaaaaaaaaaaa\U{0004}aaaa\U{0008}aaa\U{0006}a\n", "\U{0002}\0aa\U{000C}aaaaaaaaaaaaa\U{0004}aaaa\U{0008}aaa\U{0006}a\n");
expect r0 <==> isSubstringPred("\U{000C}aaaaaaaaaaaaa\U{0004}aaaa\U{0008}aaa\U{0006}a\n", "\U{0002}\0aa\U{000C}aaaaaaaaaaaaa\U{0004}aaaa\U{0008}aaa\U{0006}a\n");
}
method {:test} Test47() {
var r0 := isSubstring("\U{000C}aa\U{0008}aa\U{0002}aaaaaaaaaaaaa\naaa\U{0006}a", "\U{0004}\0");
expect r0 <==> isSubstringPred("\U{000C}aa\U{0008}aa\U{0002}aaaaaaaaaaaaa\naaa\U{0006}a", "\U{0004}\0");
}
method {:test} Test48() {
var r0 := haveCommonKSubstring(15, "aaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> haveCommonKSubstringPred(15, "aaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}");
}
method {:test} Test49() {
var r0 := haveCommonKSubstring(15, "aaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(15, "aaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test50() {
var r0 := haveCommonKSubstring(24, "\U{0012}aaaaaaaaaaa\U{0006}\U{0016}a\U{001A}a\U{000E}aaaa\na", "\U{0004}\U{0002}a\U{000C}aaaa\U{0008}\U{0010}a\0aa\U{0018}aaaaa\U{0014}a\U{001C}");
expect r0 <==> haveCommonKSubstringPred(24, "\U{0012}aaaaaaaaaaa\U{0006}\U{0016}a\U{001A}a\U{000E}aaaa\na", "\U{0004}\U{0002}a\U{000C}aaaa\U{0008}\U{0010}a\0aa\U{0018}aaaaa\U{0014}a\U{001C}");
}
method {:test} Test51() {
var r0 := haveCommonKSubstring(21, "\U{000C}aa\U{0008}a\naaa\U{0004}a\U{0006}", "\U{0002}\0");
expect r0 <==> haveCommonKSubstringPred(21, "\U{000C}aa\U{0008}a\naaa\U{0004}a\U{0006}", "\U{0002}\0");
}
method {:test} Test52() {
expect |"\U{0006}aa\U{0002}aaaaa\na\U{000C}"| <= |"\U{0004}\0aaaaaa\U{0008}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}aa\U{0002}aaaaa\na\U{000C}", "\U{0004}\0aaaaaa\U{0008}aaa");
expect forall k :: r0 < k <= |"\U{0006}aa\U{0002}aaaaa\na\U{000C}"| ==> !haveCommonKSubstringPred(k, "\U{0006}aa\U{0002}aaaaa\na\U{000C}", "\U{0004}\0aaaaaa\U{0008}aaa");
expect haveCommonKSubstringPred(r0, "\U{0006}aa\U{0002}aaaaa\na\U{000C}", "\U{0004}\0aaaaaa\U{0008}aaa");
}
method {:test} Test54() {
expect |"\U{0006}a\U{0002}\U{0008}"| <= |"\U{0004}\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}a\U{0002}\U{0008}", "\U{0004}\0aa");
expect forall k :: r0 < k <= |"\U{0006}a\U{0002}\U{0008}"| ==> !haveCommonKSubstringPred(k, "\U{0006}a\U{0002}\U{0008}", "\U{0004}\0aa");
expect haveCommonKSubstringPred(r0, "\U{0006}a\U{0002}\U{0008}", "\U{0004}\0aa");
}
method {:test} Test55() {
expect |"\U{0006}aaa"| <= |"\U{0004}a\0\U{0002}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}aaa", "\U{0004}a\0\U{0002}");
expect forall k :: r0 < k <= |"\U{0006}aaa"| ==> !haveCommonKSubstringPred(k, "\U{0006}aaa", "\U{0004}a\0\U{0002}");
expect haveCommonKSubstringPred(r0, "\U{0006}aaa", "\U{0004}a\0\U{0002}");
}

// REPEAT 4 - TIME: 28.5728835 s

method {:test} Test56() {
var r0 := isPrefix("\U{0002}\U{0004}\0aa\n\U{0008}", "\U{0002}\U{0004}\0aa\n\U{0008}\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{0002}\U{0004}\0aa\n\U{0008}", "\U{0002}\U{0004}\0aa\n\U{0008}\U{0006}");
expect r0 <==> isPrefixPred("\U{0002}\U{0004}\0aa\n\U{0008}", "\U{0002}\U{0004}\0aa\n\U{0008}\U{0006}");
}
method {:test} Test57() {
var r0 := isPrefix("\U{0004}\U{0008}\U{0006}\0", "\U{0004}\U{0008}\U{0006}\U{0002}");
expect !r0 <==> isNotPrefixPred("\U{0004}\U{0008}\U{0006}\0", "\U{0004}\U{0008}\U{0006}\U{0002}");
expect r0 <==> isPrefixPred("\U{0004}\U{0008}\U{0006}\0", "\U{0004}\U{0008}\U{0006}\U{0002}");
}
method {:test} Test58() {
var r0 := isPrefix("\U{0006}aaaa\U{0002}\n\U{000E}", "\U{0004}\0aaa\U{0008}\U{000C}");
expect !r0 <==> isNotPrefixPred("\U{0006}aaaa\U{0002}\n\U{000E}", "\U{0004}\0aaa\U{0008}\U{000C}");
expect r0 <==> isPrefixPred("\U{0006}aaaa\U{0002}\n\U{000E}", "\U{0004}\0aaa\U{0008}\U{000C}");
}
method {:test} Test59() {
var r0 := isSubstring("\U{0012}a\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\na\U{000C}\U{0010}", "\U{0004}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{000E}a");
expect r0 <==> isSubstringPred("\U{0012}a\U{0006}aaaaaaaaaaaaaaaaa\U{0008}\na\U{000C}\U{0010}", "\U{0004}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{000E}a");
}
method {:test} Test60() {
var r0 := isSubstring("\U{0006}\U{0002}", "\U{0004}\0a\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0006}\U{0002}", "\U{0004}\0a\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test61() {
var r0 := isSubstring("\U{000E}aaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaa\U{0008}aa", "\U{000C}\0a\U{0002}aaaaaaaaaaaaaaaaaa\n");
expect r0 <==> isSubstringPred("\U{000E}aaaaaaaaaaa\U{0006}aa\U{0004}aaaaaaa\U{0008}aa", "\U{000C}\0a\U{0002}aaaaaaaaaaaaaaaaaa\n");
}
method {:test} Test62() {
var r0 := haveCommonKSubstring(25, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaa\0aaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(25, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaa\0aaaaaaaaaa");
}
method {:test} Test63() {
var r0 := haveCommonKSubstring(25, "aaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(25, "aaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test64() {
var r0 := haveCommonKSubstring(25, "\U{0006}aaaaaaaaaaaaaaa\U{0002}aaaaaaaa", "\U{0004}\0");
expect r0 <==> haveCommonKSubstringPred(25, "\U{0006}aaaaaaaaaaaaaaa\U{0002}aaaaaaaa", "\U{0004}\0");
}
method {:test} Test65() {
var r0 := haveCommonKSubstring(25, "\U{0006}\U{0004}a", "\U{0008}\U{0002}\0aa");
expect r0 <==> haveCommonKSubstringPred(25, "\U{0006}\U{0004}a", "\U{0008}\U{0002}\0aa");
}
method {:test} Test66() {
expect |"\U{0002}aa\U{0006}aaaaa\n\U{000C}\U{000E}a\U{0012}"| <= |"\U{0008}\0aaaaa\U{0004}aaaa\U{0010}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aa\U{0006}aaaaa\n\U{000C}\U{000E}a\U{0012}", "\U{0008}\0aaaaa\U{0004}aaaa\U{0010}a");
expect forall k :: r0 < k <= |"\U{0002}aa\U{0006}aaaaa\n\U{000C}\U{000E}a\U{0012}"| ==> !haveCommonKSubstringPred(k, "\U{0002}aa\U{0006}aaaaa\n\U{000C}\U{000E}a\U{0012}", "\U{0008}\0aaaaa\U{0004}aaaa\U{0010}a");
expect haveCommonKSubstringPred(r0, "\U{0002}aa\U{0006}aaaaa\n\U{000C}\U{000E}a\U{0012}", "\U{0008}\0aaaaa\U{0004}aaaa\U{0010}a");
}
method {:test} Test67() {
expect |"\U{0006}aa\U{0008}aaaaa\U{000C}\U{0002}\U{000E}\U{0010}\U{0012}"| <= |"\n\0\U{0004}aaaaaaaaa\U{0014}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}aa\U{0008}aaaaa\U{000C}\U{0002}\U{000E}\U{0010}\U{0012}", "\n\0\U{0004}aaaaaaaaa\U{0014}a");
expect forall k :: r0 < k <= |"\U{0006}aa\U{0008}aaaaa\U{000C}\U{0002}\U{000E}\U{0010}\U{0012}"| ==> !haveCommonKSubstringPred(k, "\U{0006}aa\U{0008}aaaaa\U{000C}\U{0002}\U{000E}\U{0010}\U{0012}", "\n\0\U{0004}aaaaaaaaa\U{0014}a");
expect haveCommonKSubstringPred(r0, "\U{0006}aa\U{0008}aaaaa\U{000C}\U{0002}\U{000E}\U{0010}\U{0012}", "\n\0\U{0004}aaaaaaaaa\U{0014}a");
}
method {:test} Test68() {
expect |"\U{0006}\U{0002}aaaaaaa\n"| <= |"\U{0004}\0a\U{000C}aaaaa\U{0008}aaaaaa\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}\U{0002}aaaaaaa\n", "\U{0004}\0a\U{000C}aaaaa\U{0008}aaaaaa\U{000E}");
expect forall k :: r0 < k <= |"\U{0006}\U{0002}aaaaaaa\n"| ==> !haveCommonKSubstringPred(k, "\U{0006}\U{0002}aaaaaaa\n", "\U{0004}\0a\U{000C}aaaaa\U{0008}aaaaaa\U{000E}");
expect haveCommonKSubstringPred(r0, "\U{0006}\U{0002}aaaaaaa\n", "\U{0004}\0a\U{000C}aaaaa\U{0008}aaaaaa\U{000E}");
}
method {:test} Test69() {
expect |"\U{0004}\0"| <= |"\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}\0", "\U{0002}aa");
expect forall k :: r0 < k <= |"\U{0004}\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}\0", "\U{0002}aa");
expect haveCommonKSubstringPred(r0, "\U{0004}\0", "\U{0002}aa");
}

// REPEAT 5 - TIME: 36.4413567 s

method {:test} Test70() {
var r0 := isPrefix("\U{0012}\U{000E}a\U{0008}\U{0014}\U{000C}\U{0010}\U{0004}", "\U{0012}\U{000E}a\U{0008}\U{0014}\U{000C}\U{0010}\U{0004}\n\0aaaaaaaaaaa\U{0006}\U{0002}a");
expect !r0 <==> isNotPrefixPred("\U{0012}\U{000E}a\U{0008}\U{0014}\U{000C}\U{0010}\U{0004}", "\U{0012}\U{000E}a\U{0008}\U{0014}\U{000C}\U{0010}\U{0004}\n\0aaaaaaaaaaa\U{0006}\U{0002}a");
expect r0 <==> isPrefixPred("\U{0012}\U{000E}a\U{0008}\U{0014}\U{000C}\U{0010}\U{0004}", "\U{0012}\U{000E}a\U{0008}\U{0014}\U{000C}\U{0010}\U{0004}\n\0aaaaaaaaaaa\U{0006}\U{0002}a");
}
method {:test} Test71() {
var r0 := isPrefix("\n\U{0004}a\U{0002}a\U{0006}\U{0008}\0", "\U{000C}\U{0004}aaa\U{0006}a\0");
expect !r0 <==> isNotPrefixPred("\n\U{0004}a\U{0002}a\U{0006}\U{0008}\0", "\U{000C}\U{0004}aaa\U{0006}a\0");
expect r0 <==> isPrefixPred("\n\U{0004}a\U{0002}a\U{0006}\U{0008}\0", "\U{000C}\U{0004}aaa\U{0006}a\0");
}
method {:test} Test72() {
var r0 := isPrefix("\naa\U{0008}a\U{000E}\U{0014}a\U{0016}\U{0010}a", "\U{0006}\0aaa\U{000C}\U{0012}\U{0004}\U{0002}\U{0018}");
expect !r0 <==> isNotPrefixPred("\naa\U{0008}a\U{000E}\U{0014}a\U{0016}\U{0010}a", "\U{0006}\0aaa\U{000C}\U{0012}\U{0004}\U{0002}\U{0018}");
expect r0 <==> isPrefixPred("\naa\U{0008}a\U{000E}\U{0014}a\U{0016}\U{0010}a", "\U{0006}\0aaa\U{000C}\U{0012}\U{0004}\U{0002}\U{0018}");
}
method {:test} Test73() {
var r0 := isSubstring("aaaaaaaaaaaaaa\U{0002}aaaaaa\U{0004}aaa\U{0008}\U{000C}\n\U{000E}", "\U{0014}aa\0aaaaaaaaaaaaaaaaaaaa\U{0006}aa\U{0010}\U{0012}");
expect r0 <==> isSubstringPred("aaaaaaaaaaaaaa\U{0002}aaaaaa\U{0004}aaa\U{0008}\U{000C}\n\U{000E}", "\U{0014}aa\0aaaaaaaaaaaaaaaaaaaa\U{0006}aa\U{0010}\U{0012}");
}
method {:test} Test74() {
var r0 := isSubstring("\U{0002}aaaa", "\0aa\U{0002}aaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0002}aaaa", "\0aa\U{0002}aaaaaaaaaaaaaaaaa");
}
method {:test} Test75() {
var r0 := isSubstring("\U{0002}\0aaa", "\U{0004}aaa");
expect r0 <==> isSubstringPred("\U{0002}\0aaa", "\U{0004}aaa");
}
method {:test} Test76() {
var r0 := haveCommonKSubstring(26, "aaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(26, "aaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test77() {
var r0 := haveCommonKSubstring(26, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(26, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test78() {
var r0 := haveCommonKSubstring(26, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaa");
expect r0 <==> haveCommonKSubstringPred(26, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaa");
}
method {:test} Test79() {
var r0 := haveCommonKSubstring(27, "\U{0010}aaaaaaaaaa\U{000C}\U{0008}\U{000E}aaaaaaaaaaa\U{0002}", "\U{0004}\0a\U{0006}a\n");
expect r0 <==> haveCommonKSubstringPred(27, "\U{0010}aaaaaaaaaa\U{000C}\U{0008}\U{000E}aaaaaaaaaaa\U{0002}", "\U{0004}\0a\U{0006}a\n");
}
method {:test} Test80() {
expect |"aaa\U{0006}\naaaa\U{0004}\U{0002}aa\U{0010}\U{0018}\U{0016}"| <= |"\0aaaaaaaaa\U{0008}\U{000C}a\U{000E}aa\U{0014}\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaa\U{0006}\naaaa\U{0004}\U{0002}aa\U{0010}\U{0018}\U{0016}", "\0aaaaaaaaa\U{0008}\U{000C}a\U{000E}aa\U{0014}\U{0012}");
expect forall k :: r0 < k <= |"aaa\U{0006}\naaaa\U{0004}\U{0002}aa\U{0010}\U{0018}\U{0016}"| ==> !haveCommonKSubstringPred(k, "aaa\U{0006}\naaaa\U{0004}\U{0002}aa\U{0010}\U{0018}\U{0016}", "\0aaaaaaaaa\U{0008}\U{000C}a\U{000E}aa\U{0014}\U{0012}");
expect haveCommonKSubstringPred(r0, "aaa\U{0006}\naaaa\U{0004}\U{0002}aa\U{0010}\U{0018}\U{0016}", "\0aaaaaaaaa\U{0008}\U{000C}a\U{000E}aa\U{0014}\U{0012}");
}
method {:test} Test81() {
expect |"aaa\U{0004}\U{0008}aaaa\U{0002}aaa\U{000C}\U{0014}\U{0012}"| <= |"\0aaaaaaaaa\U{0006}aa\naa\U{0010}\U{000E}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaa\U{0004}\U{0008}aaaa\U{0002}aaa\U{000C}\U{0014}\U{0012}", "\0aaaaaaaaa\U{0006}aa\naa\U{0010}\U{000E}");
expect forall k :: r0 < k <= |"aaa\U{0004}\U{0008}aaaa\U{0002}aaa\U{000C}\U{0014}\U{0012}"| ==> !haveCommonKSubstringPred(k, "aaa\U{0004}\U{0008}aaaa\U{0002}aaa\U{000C}\U{0014}\U{0012}", "\0aaaaaaaaa\U{0006}aa\naa\U{0010}\U{000E}");
expect haveCommonKSubstringPred(r0, "aaa\U{0004}\U{0008}aaaa\U{0002}aaa\U{000C}\U{0014}\U{0012}", "\0aaaaaaaaa\U{0006}aa\naa\U{0010}\U{000E}");
}
method {:test} Test82() {
expect |""| <= |""|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("", "");
expect forall k :: r0 < k <= |""| ==> !haveCommonKSubstringPred(k, "", "");
expect haveCommonKSubstringPred(r0, "", "");
}
method {:test} Test83() {
expect |"\U{0002}aaaaaaaa"| <= |"\0aaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aaaaaaaa", "\0aaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0002}aaaaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0002}aaaaaaaa", "\0aaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aaaaaaaa", "\0aaaaaaaaa");
}

// REPEAT 6 - TIME: 44.7286018 s

method {:test} Test84() {
var r0 := isPrefix("\U{0010}\U{000E}\0\U{0002}a\U{0008}\n\U{0006}\U{0004}\U{000C}", "\U{0010}\U{000E}\0\U{0002}a\U{0008}\n\U{0006}\U{0004}\U{000C}");
expect !r0 <==> isNotPrefixPred("\U{0010}\U{000E}\0\U{0002}a\U{0008}\n\U{0006}\U{0004}\U{000C}", "\U{0010}\U{000E}\0\U{0002}a\U{0008}\n\U{0006}\U{0004}\U{000C}");
expect r0 <==> isPrefixPred("\U{0010}\U{000E}\0\U{0002}a\U{0008}\n\U{0006}\U{0004}\U{000C}", "\U{0010}\U{000E}\0\U{0002}a\U{0008}\n\U{0006}\U{0004}\U{000C}");
}
method {:test} Test85() {
var r0 := isPrefix("\U{0010}\U{000E}aaa\U{0006}\U{0004}\U{000C}\U{0008}\0", "\U{0010}\U{000E}aaa\U{0006}\U{0004}\U{000C}\U{0008}\U{0002}aaaaaaaaa\naaaaa");
expect !r0 <==> isNotPrefixPred("\U{0010}\U{000E}aaa\U{0006}\U{0004}\U{000C}\U{0008}\0", "\U{0010}\U{000E}aaa\U{0006}\U{0004}\U{000C}\U{0008}\U{0002}aaaaaaaaa\naaaaa");
expect r0 <==> isPrefixPred("\U{0010}\U{000E}aaa\U{0006}\U{0004}\U{000C}\U{0008}\0", "\U{0010}\U{000E}aaa\U{0006}\U{0004}\U{000C}\U{0008}\U{0002}aaaaaaaaa\naaaaa");
}
method {:test} Test86() {
var r0 := isPrefix("\U{0014}aaa\U{0002}\U{0006}\U{000E}\U{0010}aaa\U{000C}aaaaaaa\U{0008}a\naaaa", "\U{0016}\0aaaaaa\U{0012}aa\U{0004}aaaaaaaaaaaaa");
expect !r0 <==> isNotPrefixPred("\U{0014}aaa\U{0002}\U{0006}\U{000E}\U{0010}aaa\U{000C}aaaaaaa\U{0008}a\naaaa", "\U{0016}\0aaaaaa\U{0012}aa\U{0004}aaaaaaaaaaaaa");
expect r0 <==> isPrefixPred("\U{0014}aaa\U{0002}\U{0006}\U{000E}\U{0010}aaa\U{000C}aaaaaaa\U{0008}a\naaaa", "\U{0016}\0aaaaaa\U{0012}aa\U{0004}aaaaaaaaaaaaa");
}
method {:test} Test87() {
var r0 := isSubstring("\U{0012}aaaa\U{0004}aaaaaaaaaaaa\0aaaaaa\U{0008}\U{000C}a\U{000E}", "\U{0014}aaaaaaaaaaaaaaaaaaaaaa\U{0002}\naa\U{0006}\U{0010}");
expect r0 <==> isSubstringPred("\U{0012}aaaa\U{0004}aaaaaaaaaaaa\0aaaaaa\U{0008}\U{000C}a\U{000E}", "\U{0014}aaaaaaaaaaaaaaaaaaaaaa\U{0002}\naa\U{0006}\U{0010}");
}
method {:test} Test88() {
var r0 := isSubstring("\0aaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaa\0aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\0aaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaa\0aaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test89() {
var r0 := isSubstring("aaaaa\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0008}\naa", "\U{000C}aa\0aaaaaaaaaaaaaa\U{0002}aaa\U{0006}aaaa");
expect r0 <==> isSubstringPred("aaaaa\U{0004}aaaaaaaaaaaaaaaaaaaa\U{0008}\naa", "\U{000C}aa\0aaaaaaaaaaaaaa\U{0002}aaa\U{0006}aaaa");
}
method {:test} Test90() {
var r0 := haveCommonKSubstring(28, "aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(28, "aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test91() {
var r0 := haveCommonKSubstring(28, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(28, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test92() {
var r0 := haveCommonKSubstring(30, "\U{000E}aa\0aaaaaaaaaaaaa\U{0006}aaaaaaa\U{000C}a\naa", "\U{0010}aaaa\U{0002}aaaaaaaaa\U{0004}aaaaaaa\U{0008}aaaaa");
expect r0 <==> haveCommonKSubstringPred(30, "\U{000E}aa\0aaaaaaaaaaaaa\U{0006}aaaaaaa\U{000C}a\naa", "\U{0010}aaaa\U{0002}aaaaaaaaa\U{0004}aaaaaaa\U{0008}aaaaa");
}
method {:test} Test93() {
var r0 := haveCommonKSubstring(28, "\U{000E}aaaaaaaaaaaaa\U{0006}aaaaaaaa\na", "\U{000C}aaaa\U{0002}aaaaaa\0\U{0004}\U{0008}");
expect r0 <==> haveCommonKSubstringPred(28, "\U{000E}aaaaaaaaaaaaa\U{0006}aaaaaaaa\na", "\U{000C}aaaa\U{0002}aaaaaa\0\U{0004}\U{0008}");
}
method {:test} Test94() {
expect |"aaaa\U{0004}a\naaaa\U{000C}aaaaa"| <= |"\U{0006}aa\U{0002}aaa\0aaa\U{0008}a\U{000E}aaa\U{0012}\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaa\U{0004}a\naaaa\U{000C}aaaaa", "\U{0006}aa\U{0002}aaa\0aaa\U{0008}a\U{000E}aaa\U{0012}\U{0010}");
expect forall k :: r0 < k <= |"aaaa\U{0004}a\naaaa\U{000C}aaaaa"| ==> !haveCommonKSubstringPred(k, "aaaa\U{0004}a\naaaa\U{000C}aaaaa", "\U{0006}aa\U{0002}aaa\0aaa\U{0008}a\U{000E}aaa\U{0012}\U{0010}");
expect haveCommonKSubstringPred(r0, "aaaa\U{0004}a\naaaa\U{000C}aaaaa", "\U{0006}aa\U{0002}aaa\0aaa\U{0008}a\U{000E}aaa\U{0012}\U{0010}");
}
method {:test} Test95() {
expect |"aaaaa\U{0004}\naaaaaaaa\U{000C}a"| <= |"\U{0006}aa\U{0002}aaaaaaa\U{0008}a\U{000E}aa\0\U{0012}\U{0010}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaa\U{0004}\naaaaaaaa\U{000C}a", "\U{0006}aa\U{0002}aaaaaaa\U{0008}a\U{000E}aa\0\U{0012}\U{0010}");
expect forall k :: r0 < k <= |"aaaaa\U{0004}\naaaaaaaa\U{000C}a"| ==> !haveCommonKSubstringPred(k, "aaaaa\U{0004}\naaaaaaaa\U{000C}a", "\U{0006}aa\U{0002}aaaaaaa\U{0008}a\U{000E}aa\0\U{0012}\U{0010}");
expect haveCommonKSubstringPred(r0, "aaaaa\U{0004}\naaaaaaaa\U{000C}a", "\U{0006}aa\U{0002}aaaaaaa\U{0008}a\U{000E}aa\0\U{0012}\U{0010}");
}
method {:test} Test96() {
expect |"aaaaa\U{000C}\U{0004}aaa\naaa\U{000E}\U{0018}\U{0016}"| <= |"\U{0006}aa\U{0002}aaaaa\U{0008}aa\0a\U{0010}a\U{0014}\U{001A}\U{0012}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaa\U{000C}\U{0004}aaa\naaa\U{000E}\U{0018}\U{0016}", "\U{0006}aa\U{0002}aaaaa\U{0008}aa\0a\U{0010}a\U{0014}\U{001A}\U{0012}");
expect forall k :: r0 < k <= |"aaaaa\U{000C}\U{0004}aaa\naaa\U{000E}\U{0018}\U{0016}"| ==> !haveCommonKSubstringPred(k, "aaaaa\U{000C}\U{0004}aaa\naaa\U{000E}\U{0018}\U{0016}", "\U{0006}aa\U{0002}aaaaa\U{0008}aa\0a\U{0010}a\U{0014}\U{001A}\U{0012}");
expect haveCommonKSubstringPred(r0, "aaaaa\U{000C}\U{0004}aaa\naaa\U{000E}\U{0018}\U{0016}", "\U{0006}aa\U{0002}aaaaa\U{0008}aa\0a\U{0010}a\U{0014}\U{001A}\U{0012}");
}
method {:test} Test97() {
expect |"aaaaaaaa"| <= |"\0aaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaa", "\0aaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaaaa", "\0aaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaaa", "\0aaaaaaaaaaaaaaaaaa");
}

// REPEAT 7 - TIME: 53.1301305 s

method {:test} Test98() {
var r0 := isPrefix("aaaa\U{0004}\U{0002}aaaaaa\n\U{0006}a\0\U{0010}\U{000C}aa\U{000E}\U{0008}aaa\U{0014}\U{0016}\U{0018}a", "aaaa\U{0004}\U{0002}aaaaaa\n\U{0006}a\0\U{0010}\U{000C}aa\U{000E}\U{0008}aaa\U{0014}\U{0016}\U{0018}a\U{0012}");
expect !r0 <==> isNotPrefixPred("aaaa\U{0004}\U{0002}aaaaaa\n\U{0006}a\0\U{0010}\U{000C}aa\U{000E}\U{0008}aaa\U{0014}\U{0016}\U{0018}a", "aaaa\U{0004}\U{0002}aaaaaa\n\U{0006}a\0\U{0010}\U{000C}aa\U{000E}\U{0008}aaa\U{0014}\U{0016}\U{0018}a\U{0012}");
expect r0 <==> isPrefixPred("aaaa\U{0004}\U{0002}aaaaaa\n\U{0006}a\0\U{0010}\U{000C}aa\U{000E}\U{0008}aaa\U{0014}\U{0016}\U{0018}a", "aaaa\U{0004}\U{0002}aaaaaa\n\U{0006}a\0\U{0010}\U{000C}aa\U{000E}\U{0008}aaa\U{0014}\U{0016}\U{0018}a\U{0012}");
}
method {:test} Test99() {
var r0 := isPrefix("aaa\0aa\U{0006}\na\U{000E}a\U{0004}", "aaa\U{0002}aa\U{0006}aa\U{000E}\U{0008}aaaaaaaa\U{000C}aaa\U{0010}\U{0012}\U{0014}");
expect !r0 <==> isNotPrefixPred("aaa\0aa\U{0006}\na\U{000E}a\U{0004}", "aaa\U{0002}aa\U{0006}aa\U{000E}\U{0008}aaaaaaaa\U{000C}aaa\U{0010}\U{0012}\U{0014}");
expect r0 <==> isPrefixPred("aaa\0aa\U{0006}\na\U{000E}a\U{0004}", "aaa\U{0002}aa\U{0006}aa\U{000E}\U{0008}aaaaaaaa\U{000C}aaa\U{0010}\U{0012}\U{0014}");
}
method {:test} Test100() {
var r0 := isPrefix("aaa\0aaa\U{000E}a\U{0006}a\U{001A}a\U{0010}aa\U{0016}aaaaaaaa\U{0012}\U{0002}", "aaaa\U{0004}\U{000C}aaaaaaaaaa\U{0018}aa\U{0008}\naa\U{0014}a\U{001C}");
expect !r0 <==> isNotPrefixPred("aaa\0aaa\U{000E}a\U{0006}a\U{001A}a\U{0010}aa\U{0016}aaaaaaaa\U{0012}\U{0002}", "aaaa\U{0004}\U{000C}aaaaaaaaaa\U{0018}aa\U{0008}\naa\U{0014}a\U{001C}");
expect r0 <==> isPrefixPred("aaa\0aaa\U{000E}a\U{0006}a\U{001A}a\U{0010}aa\U{0016}aaaaaaaa\U{0012}\U{0002}", "aaaa\U{0004}\U{000C}aaaaaaaaaa\U{0018}aa\U{0008}\naa\U{0014}a\U{001C}");
}
method {:test} Test101() {
var r0 := isSubstring("\U{0004}aaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}aa");
expect r0 <==> isSubstringPred("\U{0004}aaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaa\0aa\U{0002}aa");
}
method {:test} Test102() {
var r0 := isSubstring("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test103() {
var r0 := isSubstring("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa", "\U{0008}aaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a");
expect r0 <==> isSubstringPred("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa", "\U{0008}aaaaaaaaaaaaaaaaaaaaaa\0\U{0002}a");
}
method {:test} Test104() {
var r0 := haveCommonKSubstring(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test105() {
var r0 := haveCommonKSubstring(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test106() {
var r0 := haveCommonKSubstring(31, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa", "\U{0006}aaaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(31, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}aa", "\U{0006}aaaaaaaaaaaaaa\U{0002}a\0aaaaaaaaaa");
}
method {:test} Test107() {
expect |"aaaaa\U{0004}aaaaa\U{0002}a\U{0006}aa\U{0008}\n"| <= |"\0aaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaa\U{0004}aaaaa\U{0002}a\U{0006}aa\U{0008}\n", "\0aaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaa\U{0004}aaaaa\U{0002}a\U{0006}aa\U{0008}\n"| ==> !haveCommonKSubstringPred(k, "aaaaa\U{0004}aaaaa\U{0002}a\U{0006}aa\U{0008}\n", "\0aaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaa\U{0004}aaaaa\U{0002}a\U{0006}aa\U{0008}\n", "\0aaaaaaaaaaaaaaaaaaa");
}
method {:test} Test108() {
expect |"aaaaa\U{0002}aaaa\U{0004}\U{0006}a\U{0008}aa\n\U{000C}"| <= |"\0aaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaa\U{0002}aaaa\U{0004}\U{0006}a\U{0008}aa\n\U{000C}", "\0aaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaa\U{0002}aaaa\U{0004}\U{0006}a\U{0008}aa\n\U{000C}"| ==> !haveCommonKSubstringPred(k, "aaaaa\U{0002}aaaa\U{0004}\U{0006}a\U{0008}aa\n\U{000C}", "\0aaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaa\U{0002}aaaa\U{0004}\U{0006}a\U{0008}aa\n\U{000C}", "\0aaaaaaaaaaaaaaaaaaa");
}
method {:test} Test109() {
expect |"aaaaaaaaaaaaaaa"| <= |"aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test110() {
expect |"\U{0002}aaaaaaaaaaaaaaaaa"| <= |"\0aaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0002}aaaaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0002}aaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaa");
}

// REPEAT 8 - TIME: 62.546073 s

method {:test} Test111() {
var r0 := isPrefix("\U{0008}\U{0006}aaa\0a\U{0002}aaa\U{0004}a", "\U{0008}\U{0006}aaa\0a\U{0002}aaa\U{0004}a");
expect !r0 <==> isNotPrefixPred("\U{0008}\U{0006}aaa\0a\U{0002}aaa\U{0004}a", "\U{0008}\U{0006}aaa\0a\U{0002}aaa\U{0004}a");
expect r0 <==> isPrefixPred("\U{0008}\U{0006}aaa\0a\U{0002}aaa\U{0004}a", "\U{0008}\U{0006}aaa\0a\U{0002}aaa\U{0004}a");
}
method {:test} Test112() {
var r0 := isPrefix("\U{0018}aaaa\U{0008}a\U{0016}a\U{0004}aa\U{0014}\U{0006}\naaa\U{0012}aaa\0\U{000C}aa\U{0010}a", "\U{0018}aaaa\U{0008}a\U{0016}a\U{0004}aa\U{0014}\U{0006}\naaa\U{0012}aaa\U{0002}\U{000C}aa\U{0010}a\U{000E}");
expect !r0 <==> isNotPrefixPred("\U{0018}aaaa\U{0008}a\U{0016}a\U{0004}aa\U{0014}\U{0006}\naaa\U{0012}aaa\0\U{000C}aa\U{0010}a", "\U{0018}aaaa\U{0008}a\U{0016}a\U{0004}aa\U{0014}\U{0006}\naaa\U{0012}aaa\U{0002}\U{000C}aa\U{0010}a\U{000E}");
expect r0 <==> isPrefixPred("\U{0018}aaaa\U{0008}a\U{0016}a\U{0004}aa\U{0014}\U{0006}\naaa\U{0012}aaa\0\U{000C}aa\U{0010}a", "\U{0018}aaaa\U{0008}a\U{0016}a\U{0004}aa\U{0014}\U{0006}\naaa\U{0012}aaa\U{0002}\U{000C}aa\U{0010}a\U{000E}");
}
method {:test} Test113() {
var r0 := isPrefix("aaaaaaa\U{0002}aaa\U{000E}aaaaaa\U{0008}\U{0004}aaaaaaa\U{0010}\U{0016}\U{0018}", "\U{001A}aaaaaaa\U{0006}aaaaaaa\U{000C}aa\0aaa\na\U{0012}\U{0014}");
expect !r0 <==> isNotPrefixPred("aaaaaaa\U{0002}aaa\U{000E}aaaaaa\U{0008}\U{0004}aaaaaaa\U{0010}\U{0016}\U{0018}", "\U{001A}aaaaaaa\U{0006}aaaaaaa\U{000C}aa\0aaa\na\U{0012}\U{0014}");
expect r0 <==> isPrefixPred("aaaaaaa\U{0002}aaa\U{000E}aaaaaa\U{0008}\U{0004}aaaaaaa\U{0010}\U{0016}\U{0018}", "\U{001A}aaaaaaa\U{0006}aaaaaaa\U{000C}aa\0aaa\na\U{0012}\U{0014}");
}
method {:test} Test114() {
var r0 := isSubstring("\U{0002}aaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0002}aaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test115() {
var r0 := isSubstring("\U{0004}aaaaa\0aaaaaaaaaaaaaa", "\U{0002}a\U{0004}aaaaa\0aaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0004}aaaaa\0aaaaaaaaaaaaaa", "\U{0002}a\U{0004}aaaaa\0aaaaaaaaaaaaaaa");
}
method {:test} Test116() {
var r0 := isSubstring("\U{000C}aaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}aaa\U{0008}", "\naaaaaaaaaaaaaaa\0aaaa\U{0002}aaaaaaa");
expect r0 <==> isSubstringPred("\U{000C}aaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}aaa\U{0008}", "\naaaaaaaaaaaaaaa\0aaaa\U{0002}aaaaaaa");
}
method {:test} Test117() {
var r0 := haveCommonKSubstring(22, "aaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(22, "aaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test119() {
var r0 := haveCommonKSubstring(32, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0008}aaaaaaaaaaaaaa\U{0002}aaa\0aaaa");
expect r0 <==> haveCommonKSubstringPred(32, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0008}aaaaaaaaaaaaaa\U{0002}aaa\0aaaa");
}
method {:test} Test120() {
expect |"aaaaaaa\naaaaaa\U{0012}\U{0008}\U{0010}aa"| <= |"\U{0002}aa\0aaa\U{0006}aaaaaaa\U{000E}\U{000C}\U{0014}aa\U{0004}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaa\naaaaaa\U{0012}\U{0008}\U{0010}aa", "\U{0002}aa\0aaa\U{0006}aaaaaaa\U{000E}\U{000C}\U{0014}aa\U{0004}");
expect forall k :: r0 < k <= |"aaaaaaa\naaaaaa\U{0012}\U{0008}\U{0010}aa"| ==> !haveCommonKSubstringPred(k, "aaaaaaa\naaaaaa\U{0012}\U{0008}\U{0010}aa", "\U{0002}aa\0aaa\U{0006}aaaaaaa\U{000E}\U{000C}\U{0014}aa\U{0004}");
expect haveCommonKSubstringPred(r0, "aaaaaaa\naaaaaa\U{0012}\U{0008}\U{0010}aa", "\U{0002}aa\0aaa\U{0006}aaaaaaa\U{000E}\U{000C}\U{0014}aa\U{0004}");
}
method {:test} Test122() {
expect |"aaaaaaaaaaaaaaaaaaa"| <= |"aaaaaaaaa\0aaaaaaa\U{0004}a\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaaaaaa", "aaaaaaaaa\0aaaaaaa\U{0004}a\U{0002}a");
expect forall k :: r0 < k <= |"aaaaaaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaaaaaaaaa", "aaaaaaaaa\0aaaaaaa\U{0004}a\U{0002}a");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaaaaaaaaa", "aaaaaaaaa\0aaaaaaa\U{0004}a\U{0002}a");
}
method {:test} Test123() {
expect |"aaaaaa\U{0002}aaaaa\U{0006}aa\U{0004}\U{0008}aa"| <= |"\0aaaaaaaaaaaaaaaa\naaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaa\U{0002}aaaaa\U{0006}aa\U{0004}\U{0008}aa", "\0aaaaaaaaaaaaaaaa\naaa");
expect forall k :: r0 < k <= |"aaaaaa\U{0002}aaaaa\U{0006}aa\U{0004}\U{0008}aa"| ==> !haveCommonKSubstringPred(k, "aaaaaa\U{0002}aaaaa\U{0006}aa\U{0004}\U{0008}aa", "\0aaaaaaaaaaaaaaaa\naaa");
expect haveCommonKSubstringPred(r0, "aaaaaa\U{0002}aaaaa\U{0006}aa\U{0004}\U{0008}aa", "\0aaaaaaaaaaaaaaaa\naaa");
}

// REPEAT 9 - TIME: 72.699222 s

method {:test} Test124() {
var r0 := isPrefix("\U{000E}aaaaaaaaaaaa\U{0004}aaa\U{0002}\U{000C}aaaa\0\U{0006}\U{0008}", "\U{000E}aaaaaaaaaaaa\U{0004}aaa\U{0002}\U{000C}aaaa\0\U{0006}\U{0008}a\n");
expect !r0 <==> isNotPrefixPred("\U{000E}aaaaaaaaaaaa\U{0004}aaa\U{0002}\U{000C}aaaa\0\U{0006}\U{0008}", "\U{000E}aaaaaaaaaaaa\U{0004}aaa\U{0002}\U{000C}aaaa\0\U{0006}\U{0008}a\n");
expect r0 <==> isPrefixPred("\U{000E}aaaaaaaaaaaa\U{0004}aaa\U{0002}\U{000C}aaaa\0\U{0006}\U{0008}", "\U{000E}aaaaaaaaaaaa\U{0004}aaa\U{0002}\U{000C}aaaa\0\U{0006}\U{0008}a\n");
}
method {:test} Test125() {
var r0 := isPrefix("\U{0010}aaaaaaaa\0aaa\U{0004}a\U{0006}a\U{0008}aaaaaaa\n\U{000C}a\U{000E}", "\U{0010}aaaaaaaa\U{0002}aaa\U{0004}a\U{0006}a\U{0008}aaaaaaa\n\U{000C}a\U{000E}");
expect !r0 <==> isNotPrefixPred("\U{0010}aaaaaaaa\0aaa\U{0004}a\U{0006}a\U{0008}aaaaaaa\n\U{000C}a\U{000E}", "\U{0010}aaaaaaaa\U{0002}aaa\U{0004}a\U{0006}a\U{0008}aaaaaaa\n\U{000C}a\U{000E}");
expect r0 <==> isPrefixPred("\U{0010}aaaaaaaa\0aaa\U{0004}a\U{0006}a\U{0008}aaaaaaa\n\U{000C}a\U{000E}", "\U{0010}aaaaaaaa\U{0002}aaa\U{0004}a\U{0006}a\U{0008}aaaaaaa\n\U{000C}a\U{000E}");
}
method {:test} Test126() {
var r0 := isPrefix("aaaaa\0a\U{0006}aaaaaaaaaaaaaaaaa", "aaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}a");
expect !r0 <==> isNotPrefixPred("aaaaa\0a\U{0006}aaaaaaaaaaaaaaaaa", "aaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}a");
expect r0 <==> isPrefixPred("aaaaa\0a\U{0006}aaaaaaaaaaaaaaaaa", "aaaaaaaaa\U{0002}aaaaaaaaaaa\U{0004}a");
}
method {:test} Test127() {
var r0 := isSubstring("\U{0002}aaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0002}aaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test128() {
var r0 := isSubstring("aaaaaaa\U{0002}", "\U{0004}aaa\0aaaaaaa\U{0002}aaaaaaaaaa");
expect r0 <==> isSubstringPred("aaaaaaa\U{0002}", "\U{0004}aaa\0aaaaaaa\U{0002}aaaaaaaaaa");
}
method {:test} Test129() {
var r0 := isSubstring("\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test130() {
var r0 := haveCommonKSubstring(23, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(23, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test132() {
var r0 := haveCommonKSubstring(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaa");
}
method {:test} Test133() {
var r0 := haveCommonKSubstring(33, "\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aaaa", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}");
expect r0 <==> haveCommonKSubstringPred(33, "\U{0006}aaaaaaaaaaaaaaaaaaaaaa\0aaaa", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}");
}
method {:test} Test134() {
expect |"aaaaaaaaaaaaaaa\U{0006}a\U{0004}a\n"| <= |"\0aaaaaaaaaaaaa\U{0002}aaaaa\U{0008}\U{000C}"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaa\U{0006}a\U{0004}a\n", "\0aaaaaaaaaaaaa\U{0002}aaaaa\U{0008}\U{000C}");
expect forall k :: r0 < k <= |"aaaaaaaaaaaaaaa\U{0006}a\U{0004}a\n"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaaaaa\U{0006}a\U{0004}a\n", "\0aaaaaaaaaaaaa\U{0002}aaaaa\U{0008}\U{000C}");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaaaaa\U{0006}a\U{0004}a\n", "\0aaaaaaaaaaaaa\U{0002}aaaaa\U{0008}\U{000C}");
}
method {:test} Test136() {
expect |"\0aaaa"| <= |"\U{0002}aaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0aaaa", "\U{0002}aaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\0aaaa"| ==> !haveCommonKSubstringPred(k, "\0aaaa", "\U{0002}aaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\0aaaa", "\U{0002}aaaaaaaaaaaaaaaaa");
}
method {:test} Test137() {
expect |"aaaaaaaaaaaaaaa\U{0002}aa\0a"| <= |"aaaaaaaaaaaaaaa\U{0004}aaa\U{0006}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaa\U{0002}aa\0a", "aaaaaaaaaaaaaaa\U{0004}aaa\U{0006}aa");
expect forall k :: r0 < k <= |"aaaaaaaaaaaaaaa\U{0002}aa\0a"| ==> !haveCommonKSubstringPred(k, "aaaaaaaaaaaaaaa\U{0002}aa\0a", "aaaaaaaaaaaaaaa\U{0004}aaa\U{0006}aa");
expect haveCommonKSubstringPred(r0, "aaaaaaaaaaaaaaa\U{0002}aa\0a", "aaaaaaaaaaaaaaa\U{0004}aaa\U{0006}aa");
}

// REPEAT 10 - TIME: 84.2362017 s

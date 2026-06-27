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
var r0 := isPrefix("a", "a");
expect !r0 <==> isNotPrefixPred("a", "a");
expect r0 <==> isPrefixPred("a", "a");
}
method {:test} Test2() {
var r0 := isSubstring("a", "aaaaaaaaaaa");
expect r0 <==> isSubstringPred("a", "aaaaaaaaaaa");
}
method {:test} Test3() {
var r0 := isSubstring("", "");
expect r0 <==> isSubstringPred("", "");
}
method {:test} Test4() {
var r0 := haveCommonKSubstring(6, "aaaaaaaaaaaa", "aaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(6, "aaaaaaaaaaaa", "aaaaaaaaaaaaaaaaa");
}
method {:test} Test5() {
var r0 := haveCommonKSubstring(38, "", "");
expect r0 <==> haveCommonKSubstringPred(38, "", "");
}
method {:test} Test6() {
expect |"aaaaaa"| <= |"aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaa", "aaaaaaa");
expect forall k :: r0 < k <= |"aaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaa", "aaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaa", "aaaaaaa");
}

// REPEAT 1 - TIME: 8.3040937 s

method {:test} Test7() {
var r0 := isPrefix("\U{0002}\0aaaaaaaaaaaaaaaaa", "");
expect !r0 <==> isNotPrefixPred("\U{0002}\0aaaaaaaaaaaaaaaaa", "");
expect r0 <==> isPrefixPred("\U{0002}\0aaaaaaaaaaaaaaaaa", "");
}
method {:test} Test8() {
var r0 := isPrefix("a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}", "a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}");
expect !r0 <==> isNotPrefixPred("a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}", "a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}");
expect r0 <==> isPrefixPred("a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}", "a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}");
}
method {:test} Test9() {
var r0 := isSubstring("aa\U{0002}", "\U{0004}aa\U{0002}\0");
expect r0 <==> isSubstringPred("aa\U{0002}", "\U{0004}aa\U{0002}\0");
}
method {:test} Test10() {
var r0 := isSubstring("a\0", "\U{0002}");
expect r0 <==> isSubstringPred("a\0", "\U{0002}");
}
method {:test} Test11() {
var r0 := haveCommonKSubstring(7, "aaaaaaaa", "\0aaaaaaa");
expect r0 <==> haveCommonKSubstringPred(7, "aaaaaaaa", "\0aaaaaaa");
}
method {:test} Test12() {
var r0 := haveCommonKSubstring(39, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}");
expect r0 <==> haveCommonKSubstringPred(39, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}");
}
method {:test} Test13() {
expect |"\0aaaaaaaaaaaaaaaaaaaa"| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0aaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\0aaaaaaaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "\0aaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\0aaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 2 - TIME: 13.2941879 s

method {:test} Test14() {
var r0 := isPrefix("aaaaaaaaaaaaaa\U{0002}aaaa\U{0004}", "\U{0006}\0");
expect !r0 <==> isNotPrefixPred("aaaaaaaaaaaaaa\U{0002}aaaa\U{0004}", "\U{0006}\0");
expect r0 <==> isPrefixPred("aaaaaaaaaaaaaa\U{0002}aaaa\U{0004}", "\U{0006}\0");
}
method {:test} Test15() {
var r0 := isPrefix("\U{0006}\0aaaaaaaaaaaaaa\U{0004}aa\U{0002}", "\U{0006}\0aaaaaaaaaaaaaa\U{0004}aa\U{0002}");
expect !r0 <==> isNotPrefixPred("\U{0006}\0aaaaaaaaaaaaaa\U{0004}aa\U{0002}", "\U{0006}\0aaaaaaaaaaaaaa\U{0004}aa\U{0002}");
expect r0 <==> isPrefixPred("\U{0006}\0aaaaaaaaaaaaaa\U{0004}aa\U{0002}", "\U{0006}\0aaaaaaaaaaaaaa\U{0004}aa\U{0002}");
}
method {:test} Test16() {
var r0 := isSubstring("\U{0004}aa\U{0002}", "aaaaa\0\U{0004}aa\U{0002}");
expect r0 <==> isSubstringPred("\U{0004}aa\U{0002}", "aaaaa\0\U{0004}aa\U{0002}");
}
method {:test} Test17() {
var r0 := isSubstring("a\U{0004}\U{0002}a", "aaaa\0\U{0006}");
expect r0 <==> isSubstringPred("a\U{0004}\U{0002}a", "aaaa\0\U{0006}");
}
method {:test} Test18() {
var r0 := haveCommonKSubstring(8, "\U{0004}aaaaaaaa", "\U{0002}aa\0aaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(8, "\U{0004}aaaaaaaa", "\U{0002}aa\0aaaaaaaaaa");
}
method {:test} Test19() {
var r0 := haveCommonKSubstring(40, "\naaaaa\U{0002}a\U{0004}aaa\U{0006}", "\U{0008}\0");
expect r0 <==> haveCommonKSubstringPred(40, "\naaaaa\U{0002}a\U{0004}aaa\U{0006}", "\U{0008}\0");
}
method {:test} Test20() {
expect |"\0aaaaaaaaaaaaaaaaaaaa\U{0004}a"| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0aaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\0aaaaaaaaaaaaaaaaaaaa\U{0004}a"| ==> !haveCommonKSubstringPred(k, "\0aaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\0aaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 3 - TIME: 17.3427212 s

method {:test} Test21() {
var r0 := isPrefix("\U{0006}aa\U{0002}a", "\U{0008}\0a\U{0004}");
expect !r0 <==> isNotPrefixPred("\U{0006}aa\U{0002}a", "\U{0008}\0a\U{0004}");
expect r0 <==> isPrefixPred("\U{0006}aa\U{0002}a", "\U{0008}\0a\U{0004}");
}
method {:test} Test22() {
var r0 := isPrefix("\U{0008}\U{0002}aaaaa\0aaa\U{0004}aaaaaa", "\U{0008}\U{0002}aaaaa\0aaa\U{0004}aaaaaaaa\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{0008}\U{0002}aaaaa\0aaa\U{0004}aaaaaa", "\U{0008}\U{0002}aaaaa\0aaa\U{0004}aaaaaaaa\U{0006}");
expect r0 <==> isPrefixPred("\U{0008}\U{0002}aaaaa\0aaa\U{0004}aaaaaa", "\U{0008}\U{0002}aaaaa\0aaa\U{0004}aaaaaaaa\U{0006}");
}
method {:test} Test23() {
var r0 := isSubstring("\U{0004}aa\U{0006}a\U{0002}", "\U{0008}\0\U{0004}aa\U{0006}a\U{0002}");
expect r0 <==> isSubstringPred("\U{0004}aa\U{0006}a\U{0002}", "\U{0008}\0\U{0004}aa\U{0006}a\U{0002}");
}
method {:test} Test24() {
var r0 := isSubstring("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\n\U{0002}aa\0\U{0008}");
expect r0 <==> isSubstringPred("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\n\U{0002}aa\0\U{0008}");
}
method {:test} Test25() {
var r0 := haveCommonKSubstring(9, "\U{0006}aaaaaaaaa", "\U{0004}\U{0002}aaaaa\0aaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(9, "\U{0006}aaaaaaaaa", "\U{0004}\U{0002}aaaaa\0aaaaaaaaaa");
}
method {:test} Test26() {
var r0 := haveCommonKSubstring(41, "\U{0004}", "\U{0002}\0");
expect r0 <==> haveCommonKSubstringPred(41, "\U{0004}", "\U{0002}\0");
}
method {:test} Test27() {
expect |"\U{0004}aaaaa\0"| <= |"\U{0002}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaa\0", "\U{0002}aaaaaaaa");
expect forall k :: r0 < k <= |"\U{0004}aaaaa\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaa\0", "\U{0002}aaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaa\0", "\U{0002}aaaaaaaa");
}

// REPEAT 4 - TIME: 21.2029808 s

method {:test} Test28() {
var r0 := isPrefix("\naaaa\U{0004}aaaaaa", "\U{0008}\U{0002}a\U{0006}aaaaa\0");
expect !r0 <==> isNotPrefixPred("\naaaa\U{0004}aaaaaa", "\U{0008}\U{0002}a\U{0006}aaaaa\0");
expect r0 <==> isPrefixPred("\naaaa\U{0004}aaaaaa", "\U{0008}\U{0002}a\U{0006}aaaaa\0");
}
method {:test} Test29() {
var r0 := isPrefix("\U{0002}\0", "\U{0002}\0");
expect !r0 <==> isNotPrefixPred("\U{0002}\0", "\U{0002}\0");
expect r0 <==> isPrefixPred("\U{0002}\0", "\U{0002}\0");
}
method {:test} Test30() {
var r0 := isSubstring("\U{0004}aaaa\U{0006}a\0", "\U{0008}\U{0002}\U{0004}aaaa\U{0006}a\0");
expect r0 <==> isSubstringPred("\U{0004}aaaa\U{0006}a\0", "\U{0008}\U{0002}\U{0004}aaaa\U{0006}a\0");
}
method {:test} Test31() {
var r0 := isSubstring("\U{0006}aaa\U{0004}", "\U{0008}\U{0002}aa\0a");
expect r0 <==> isSubstringPred("\U{0006}aaa\U{0004}", "\U{0008}\U{0002}aa\0a");
}
method {:test} Test32() {
var r0 := haveCommonKSubstring(10, "a\0aaaaaaa\U{0008}a\n\U{000C}\U{000E}aaaaaaaaaaaaaaa\U{0012}", "\U{0002}aaaaaa\U{0004}aaaaaaa\U{0006}a\U{0010}aaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(10, "a\0aaaaaaa\U{0008}a\n\U{000C}\U{000E}aaaaaaaaaaaaaaa\U{0012}", "\U{0002}aaaaaa\U{0004}aaaaaaa\U{0006}a\U{0010}aaaaaaaaaaa");
}
method {:test} Test33() {
var r0 := haveCommonKSubstring(42, "\U{0006}\0", "\U{0008}aa\U{0002}aaaa\U{0004}");
expect r0 <==> haveCommonKSubstringPred(42, "\U{0006}\0", "\U{0008}aa\U{0002}aaaa\U{0004}");
}
method {:test} Test34() {
expect |"\0a"| <= |"\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0a", "\U{0002}a");
expect forall k :: r0 < k <= |"\0a"| ==> !haveCommonKSubstringPred(k, "\0a", "\U{0002}a");
expect haveCommonKSubstringPred(r0, "\0a", "\U{0002}a");
}

// REPEAT 5 - TIME: 25.8259138 s

method {:test} Test35() {
var r0 := isPrefix("a\U{0002}aaaaaaaaaaaaaaaaa\U{000E}\U{0010}\U{000C}\U{0016}a", "\U{0004}\0aaaaaaa\U{0008}aa\naaaaa\U{0006}aa\U{0012}\U{0014}");
expect !r0 <==> isNotPrefixPred("a\U{0002}aaaaaaaaaaaaaaaaa\U{000E}\U{0010}\U{000C}\U{0016}a", "\U{0004}\0aaaaaaa\U{0008}aa\naaaaa\U{0006}aa\U{0012}\U{0014}");
expect r0 <==> isPrefixPred("a\U{0002}aaaaaaaaaaaaaaaaa\U{000E}\U{0010}\U{000C}\U{0016}a", "\U{0004}\0aaaaaaa\U{0008}aa\naaaaa\U{0006}aa\U{0012}\U{0014}");
}
method {:test} Test36() {
var r0 := isPrefix("\U{0004}\U{0002}\0a", "\U{0004}\U{0002}\0aa");
expect !r0 <==> isNotPrefixPred("\U{0004}\U{0002}\0a", "\U{0004}\U{0002}\0aa");
expect r0 <==> isPrefixPred("\U{0004}\U{0002}\0a", "\U{0004}\U{0002}\0aa");
}
method {:test} Test37() {
var r0 := isSubstring("\U{0008}\0aa\U{0004}a\U{0002}a\n", "aaaaa\U{0006}aaaaa\U{000C}aaaaaaa\U{0008}\0aa\U{0004}a\U{0002}a\n");
expect r0 <==> isSubstringPred("\U{0008}\0aa\U{0004}a\U{0002}a\n", "aaaaa\U{0006}aaaaa\U{000C}aaaaaaa\U{0008}\0aa\U{0004}a\U{0002}a\n");
}
method {:test} Test38() {
var r0 := isSubstring("\U{0002}\0", "\U{0006}aaaa\U{0004}a");
expect r0 <==> isSubstringPred("\U{0002}\0", "\U{0006}aaaa\U{0004}a");
}
method {:test} Test39() {
var r0 := haveCommonKSubstring(11, "\U{0008}aa\U{0006}\U{0002}aaaaaaaaaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(11, "\U{0008}aa\U{0006}\U{0002}aaaaaaaaaaaa", "\U{0004}\0aaaaaaaaaaaaaaaaaaa");
}
method {:test} Test40() {
var r0 := haveCommonKSubstring(43, "\U{0012}aaaaaaaa\U{0008}aaaaa\U{000C}aaa\U{0002}aaaaaaaaa\U{000E}", "\U{0010}\0aaaa\U{0006}\U{0004}aaaaaaaaaaaaaaaa\n");
expect r0 <==> haveCommonKSubstringPred(43, "\U{0012}aaaaaaaa\U{0008}aaaaa\U{000C}aaa\U{0002}aaaaaaaaa\U{000E}", "\U{0010}\0aaaa\U{0006}\U{0004}aaaaaaaaaaaaaaaa\n");
}
method {:test} Test41() {
expect |"\U{0004}aa\0aaaaaaaaa"| <= |"\U{0002}aaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aa\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0004}aa\0aaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0004}aa\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aa\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaaaa");
}

// REPEAT 6 - TIME: 29.9506869 s

method {:test} Test42() {
var r0 := isPrefix("\U{0004}aaa\U{0002}", "\U{0006}\0a");
expect !r0 <==> isNotPrefixPred("\U{0004}aaa\U{0002}", "\U{0006}\0a");
expect r0 <==> isPrefixPred("\U{0004}aaa\U{0002}", "\U{0006}\0a");
}
method {:test} Test43() {
var r0 := isPrefix("\U{0004}\U{0002}\0", "\U{0004}\U{0002}\0");
expect !r0 <==> isNotPrefixPred("\U{0004}\U{0002}\0", "\U{0004}\U{0002}\0");
expect r0 <==> isPrefixPred("\U{0004}\U{0002}\0", "\U{0004}\U{0002}\0");
}
method {:test} Test44() {
var r0 := isSubstring("\U{0002}\0a", "\U{0004}a\U{0002}\0a");
expect r0 <==> isSubstringPred("\U{0002}\0a", "\U{0004}a\U{0002}\0a");
}
method {:test} Test45() {
var r0 := isSubstring("\U{0006}a\U{0002}aa\U{0008}\U{000C}", "\U{0014}\U{0004}aaa\na\U{0010}a\U{0012}\U{000E}\0");
expect r0 <==> isSubstringPred("\U{0006}a\U{0002}aa\U{0008}\U{000C}", "\U{0014}\U{0004}aaa\na\U{0010}a\U{0012}\U{000E}\0");
}
method {:test} Test46() {
var r0 := haveCommonKSubstring(14, "\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa", "\U{0006}\0aaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(14, "\U{0004}aaaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa", "\U{0006}\0aaaaaaaaaaaaaaaaa");
}
method {:test} Test47() {
var r0 := haveCommonKSubstring(44, "\U{000E}aa\U{0006}aaaaa\U{0008}aaa\U{000C}aaaaa\naaaaaaaa\U{0012}\U{0002}", "\U{0010}\0\U{0004}");
expect r0 <==> haveCommonKSubstringPred(44, "\U{000E}aa\U{0006}aaaaa\U{0008}aaa\U{000C}aaaaa\naaaaaaaa\U{0012}\U{0002}", "\U{0010}\0\U{0004}");
}
method {:test} Test48() {
expect |"\U{0006}aaaaa\0aaaaaaa"| <= |"\U{0004}aaaaaaaaaaa\U{0002}aaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}aaaaa\0aaaaaaa", "\U{0004}aaaaaaaaaaa\U{0002}aaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0006}aaaaa\0aaaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0006}aaaaa\0aaaaaaa", "\U{0004}aaaaaaaaaaa\U{0002}aaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0006}aaaaa\0aaaaaaa", "\U{0004}aaaaaaaaaaa\U{0002}aaaaaaaaa");
}

// REPEAT 7 - TIME: 35.2732005 s

method {:test} Test49() {
var r0 := isPrefix("\U{000C}aaaaaaa\U{0006}aa\U{0008}a\U{0002}a", "\U{000E}\0a\U{0004}\n");
expect !r0 <==> isNotPrefixPred("\U{000C}aaaaaaa\U{0006}aa\U{0008}a\U{0002}a", "\U{000E}\0a\U{0004}\n");
expect r0 <==> isPrefixPred("\U{000C}aaaaaaa\U{0006}aa\U{0008}a\U{0002}a", "\U{000E}\0a\U{0004}\n");
}
method {:test} Test50() {
var r0 := isPrefix("\U{0002}\0", "\U{0002}\0");
expect !r0 <==> isNotPrefixPred("\U{0002}\0", "\U{0002}\0");
expect r0 <==> isPrefixPred("\U{0002}\0", "\U{0002}\0");
}
method {:test} Test51() {
var r0 := isSubstring("\U{000C}aaa\naa\U{0004}\U{0006}a\U{0012}\U{000E}\U{0008}", "a\U{0002}aaaa\0\U{0010}aaa\U{0014}\U{0016}\U{000C}aaa\naa\U{0004}\U{0006}a\U{0012}\U{000E}\U{0008}");
expect r0 <==> isSubstringPred("\U{000C}aaa\naa\U{0004}\U{0006}a\U{0012}\U{000E}\U{0008}", "a\U{0002}aaaa\0\U{0010}aaa\U{0014}\U{0016}\U{000C}aaa\naa\U{0004}\U{0006}a\U{0012}\U{000E}\U{0008}");
}
method {:test} Test52() {
var r0 := isSubstring("\naa\0a\U{0006}\U{0004}\U{0002}", "\U{0008}a");
expect r0 <==> isSubstringPred("\naa\0a\U{0006}\U{0004}\U{0002}", "\U{0008}a");
}
method {:test} Test53() {
var r0 := haveCommonKSubstring(16, "\U{0008}aaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\na", "\U{0006}\U{0002}aaa\0aaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(16, "\U{0008}aaaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa\na", "\U{0006}\U{0002}aaa\0aaaaaaaaaaaaaaaaaa");
}
method {:test} Test54() {
var r0 := haveCommonKSubstring(45, "\U{001E}\U{0004}aaaaaaaa\U{000C}aaaa\U{0012}a\U{0016}aaa\U{000E}aaaaaa\U{0002}", " aaaaaa\U{0008}\U{0006}\U{0010}a\naaaaaaa\U{001A}a\U{001C}a\U{0018}\U{0014}\0");
expect r0 <==> haveCommonKSubstringPred(45, "\U{001E}\U{0004}aaaaaaaa\U{000C}aaaa\U{0012}a\U{0016}aaa\U{000E}aaaaaa\U{0002}", " aaaaaa\U{0008}\U{0006}\U{0010}a\naaaaaaa\U{001A}a\U{001C}a\U{0018}\U{0014}\0");
}
method {:test} Test55() {
expect |"\U{0006}aaaaaa\U{0002}aaaaaa"| <= |"\0aaaaaa\U{0004}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}aaaaaa\U{0002}aaaaaa", "\0aaaaaa\U{0004}aaaaaa");
expect forall k :: r0 < k <= |"\U{0006}aaaaaa\U{0002}aaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0006}aaaaaa\U{0002}aaaaaa", "\0aaaaaa\U{0004}aaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0006}aaaaaa\U{0002}aaaaaa", "\0aaaaaa\U{0004}aaaaaa");
}

// REPEAT 8 - TIME: 40.0168707 s

method {:test} Test56() {
var r0 := isPrefix("\U{0012}a\U{0004}aa\U{0008}aaaa\U{000C}a\U{000E}", "\U{0010}\0a\U{0002}\U{0006}\n");
expect !r0 <==> isNotPrefixPred("\U{0012}a\U{0004}aa\U{0008}aaaa\U{000C}a\U{000E}", "\U{0010}\0a\U{0002}\U{0006}\n");
expect r0 <==> isPrefixPred("\U{0012}a\U{0004}aa\U{0008}aaaa\U{000C}a\U{000E}", "\U{0010}\0a\U{0002}\U{0006}\n");
}
method {:test} Test57() {
var r0 := isPrefix("\0\U{0002}", "\0\U{0002}");
expect !r0 <==> isNotPrefixPred("\0\U{0002}", "\0\U{0002}");
expect r0 <==> isPrefixPred("\0\U{0002}", "\0\U{0002}");
}
method {:test} Test58() {
var r0 := isSubstring("\U{0008}aaaaa\U{000C}\U{0006}a\na\U{0014}\U{0010}\U{001A}", "a\U{0004}a\U{0002}aaaa\U{0016}\U{000E}\0\U{0018}\U{0012}\U{0008}aaaaa\U{000C}\U{0006}a\na\U{0014}\U{0010}\U{001A}");
expect r0 <==> isSubstringPred("\U{0008}aaaaa\U{000C}\U{0006}a\na\U{0014}\U{0010}\U{001A}", "a\U{0004}a\U{0002}aaaa\U{0016}\U{000E}\0\U{0018}\U{0012}\U{0008}aaaaa\U{000C}\U{0006}a\na\U{0014}\U{0010}\U{001A}");
}
method {:test} Test59() {
var r0 := isSubstring("\U{0006}aa\U{0002}\U{0004}\U{000E}a\n\U{000C}", "\U{0010}\0\U{0008}");
expect r0 <==> isSubstringPred("\U{0006}aa\U{0002}\U{0004}\U{000E}a\n\U{000C}", "\U{0010}\0\U{0008}");
}
method {:test} Test60() {
var r0 := haveCommonKSubstring(17, "\U{0012}aaaaaaaa\U{0008}aaaaaaaaaaaaaaaaa\U{000E}\n", "a\U{0002}aaaa\U{0004}\0a\U{0006}aaaaaaaa\U{000C}aaaaaa\U{0010}a\U{000E}");
expect r0 <==> haveCommonKSubstringPred(17, "\U{0012}aaaaaaaa\U{0008}aaaaaaaaaaaaaaaaa\U{000E}\n", "a\U{0002}aaaa\U{0004}\0a\U{0006}aaaaaaaa\U{000C}aaaaaa\U{0010}a\U{000E}");
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(46, "\U{0008}\U{0002}aaaaaaaaaa", "\U{0006}a\U{0004}\0");
expect r0 <==> haveCommonKSubstringPred(46, "\U{0008}\U{0002}aaaaaaaaaa", "\U{0006}a\U{0004}\0");
}
method {:test} Test62() {
expect |"\U{0004}aaaaa\0"| <= |"\U{0002}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaa\0", "\U{0002}aaaaaa");
expect forall k :: r0 < k <= |"\U{0004}aaaaa\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaa\0", "\U{0002}aaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaa\0", "\U{0002}aaaaaa");
}

// REPEAT 9 - TIME: 46.3849757 s

method {:test} Test63() {
var r0 := isPrefix("\U{0018}aaa\naaaaaaa\U{0014}\U{0012}a\U{0016}a", "\U{001A}\U{0002}\U{0004}aa\U{000C}\U{000E}\U{0006}a\U{0008}\0\U{0010}");
expect !r0 <==> isNotPrefixPred("\U{0018}aaa\naaaaaaa\U{0014}\U{0012}a\U{0016}a", "\U{001A}\U{0002}\U{0004}aa\U{000C}\U{000E}\U{0006}a\U{0008}\0\U{0010}");
expect r0 <==> isPrefixPred("\U{0018}aaa\naaaaaaa\U{0014}\U{0012}a\U{0016}a", "\U{001A}\U{0002}\U{0004}aa\U{000C}\U{000E}\U{0006}a\U{0008}\0\U{0010}");
}
method {:test} Test64() {
var r0 := isPrefix("\U{0002}\0a", "\U{0002}\0a");
expect !r0 <==> isNotPrefixPred("\U{0002}\0a", "\U{0002}\0a");
expect r0 <==> isPrefixPred("\U{0002}\0a", "\U{0002}\0a");
}
method {:test} Test65() {
var r0 := isSubstring("\U{0004}aa\U{0006}\n\U{0002}", "\U{000C}\0\U{0008}\U{0004}aa\U{0006}\n\U{0002}");
expect r0 <==> isSubstringPred("\U{0004}aa\U{0006}\n\U{0002}", "\U{000C}\0\U{0008}\U{0004}aa\U{0006}\n\U{0002}");
}
method {:test} Test66() {
var r0 := isSubstring("\U{0006}\0a\U{0004}\n\U{0008}", "\U{000C}\U{0002}aa");
expect r0 <==> isSubstringPred("\U{0006}\0a\U{0004}\n\U{0008}", "\U{000C}\U{0002}aa");
}
method {:test} Test67() {
var r0 := haveCommonKSubstring(18, "\U{0018}aa\U{0004}aaaaa\n\U{000C}aaaaaaaaaaaaaaaaaa\U{0016}", "a\0aaaa\U{0002}\U{0006}\U{0008}aaaaaaaaa\U{0010}aa\U{0012}aaaaa\U{0016}\U{000E}\U{0014}");
expect r0 <==> haveCommonKSubstringPred(18, "\U{0018}aa\U{0004}aaaaa\n\U{000C}aaaaaaaaaaaaaaaaaa\U{0016}", "a\0aaaa\U{0002}\U{0006}\U{0008}aaaaaaaaa\U{0010}aa\U{0012}aaaaa\U{0016}\U{000E}\U{0014}");
}
method {:test} Test68() {
var r0 := haveCommonKSubstring(47, "\U{000E}\0a\U{0002}aaaaaaa\U{0008}\na", "\U{000C}aaaaaaaa\U{0006}a\U{0004}aaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(47, "\U{000E}\0a\U{0002}aaaaaaa\U{0008}\na", "\U{000C}aaaaaaaa\U{0006}a\U{0004}aaaaaaaa");
}
method {:test} Test69() {
expect |"\0a"| <= |"\U{0002}aaaaaa\U{0004}aaaaaa\U{0006}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0a", "\U{0002}aaaaaa\U{0004}aaaaaa\U{0006}aaa");
expect forall k :: r0 < k <= |"\0a"| ==> !haveCommonKSubstringPred(k, "\0a", "\U{0002}aaaaaa\U{0004}aaaaaa\U{0006}aaa");
expect haveCommonKSubstringPred(r0, "\0a", "\U{0002}aaaaaa\U{0004}aaaaaa\U{0006}aaa");
}

// REPEAT 10 - TIME: 51.502007 s

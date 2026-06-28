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
  if |pre| >= |str| {
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

// REPEAT 1 - TIME: 8.5017332 s

method {:test} Test7() {
var r0 := isPrefix("\U{0002}\0aaaaaa\U{0004}aa", "");
expect !r0 <==> isNotPrefixPred("\U{0002}\0aaaaaa\U{0004}aa", "");
expect r0 <==> isPrefixPred("\U{0002}\0aaaaaa\U{0004}aa", "");
}
method {:test} Test8() {
var r0 := isPrefix("a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}", "a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}");
expect !r0 <==> isNotPrefixPred("a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}", "a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}");
expect r0 <==> isPrefixPred("a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}", "a\0aaaaaaaaaaaaaaaa\U{0002}aa\U{0004}");
}
method {:test} Test9() {
var r0 := isSubstring("aaaaaaaaaaaaaaaaa\0aaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaa");
expect r0 <==> isSubstringPred("aaaaaaaaaaaaaaaaa\0aaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaa\0aaaaaaa");
}
method {:test} Test10() {
var r0 := isSubstring("a\0", "a");
expect r0 <==> isSubstringPred("a\0", "a");
}
method {:test} Test11() {
var r0 := haveCommonKSubstring(7, "\U{0002}aaaaaaa", "aaaaaaaaaaaaaaa\0");
expect r0 <==> haveCommonKSubstringPred(7, "\U{0002}aaaaaaa", "aaaaaaaaaaaaaaa\0");
}
method {:test} Test12() {
var r0 := haveCommonKSubstring(39, "\0", "\U{0002}");
expect r0 <==> haveCommonKSubstringPred(39, "\0", "\U{0002}");
}
method {:test} Test13() {
expect |"aaaaaa\0"| <= |"aaaaaaa\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaa\0", "aaaaaaa\U{0002}a");
expect forall k :: r0 < k <= |"aaaaaa\0"| ==> !haveCommonKSubstringPred(k, "aaaaaa\0", "aaaaaaa\U{0002}a");
expect haveCommonKSubstringPred(r0, "aaaaaa\0", "aaaaaaa\U{0002}a");
}

// REPEAT 2 - TIME: 13.7524456 s

method {:test} Test14() {
var r0 := isPrefix("\U{0004}a\U{0002}aaaaaaa", "\U{0006}\0");
expect !r0 <==> isNotPrefixPred("\U{0004}a\U{0002}aaaaaaa", "\U{0006}\0");
expect r0 <==> isPrefixPred("\U{0004}a\U{0002}aaaaaaa", "\U{0006}\0");
}
method {:test} Test15() {
var r0 := isPrefix("\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0");
expect !r0 <==> isNotPrefixPred("\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> isPrefixPred("\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaa\0");
}
method {:test} Test16() {
var r0 := isSubstring("\U{0006}\U{0002}", "\U{0008}aaaaaaaaaa\U{0004}aaaa\0aaaaaaaaa\na\U{0006}\U{0002}");
expect r0 <==> isSubstringPred("\U{0006}\U{0002}", "\U{0008}aaaaaaaaaa\U{0004}aaaa\0aaaaaaaaa\na\U{0006}\U{0002}");
}
method {:test} Test17() {
var r0 := isSubstring("\U{0008}aaaaaaaaaa\U{0004}aaaa\0", "\n\U{0002}aaaaaaaaa\U{0006}");
expect r0 <==> isSubstringPred("\U{0008}aaaaaaaaaa\U{0004}aaaa\0", "\n\U{0002}aaaaaaaaa\U{0006}");
}
method {:test} Test18() {
var r0 := haveCommonKSubstring(8, "\U{0004}aaaaaaaaaaaaaaaa\0", "\U{0006}\U{0002}aaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(8, "\U{0004}aaaaaaaaaaaaaaaa\0", "\U{0006}\U{0002}aaaaaaaaaaaa");
}
method {:test} Test19() {
var r0 := haveCommonKSubstring(40, "\U{0004}aaaaaaaa\0aa\U{0006}", "\U{0008}\U{0002}");
expect r0 <==> haveCommonKSubstringPred(40, "\U{0004}aaaaaaaa\0aa\U{0006}", "\U{0008}\U{0002}");
}
method {:test} Test20() {
expect |"aaaaaaa\0"| <= |"\U{0002}aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaa\0", "\U{0002}aaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaa\0"| ==> !haveCommonKSubstringPred(k, "aaaaaaa\0", "\U{0002}aaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaa\0", "\U{0002}aaaaaaa");
}

// REPEAT 3 - TIME: 18.4457429 s

method {:test} Test21() {
var r0 := isPrefix("\U{0006}\U{0002}aa", "\U{0004}\0a");
expect !r0 <==> isNotPrefixPred("\U{0006}\U{0002}aa", "\U{0004}\0a");
expect r0 <==> isPrefixPred("\U{0006}\U{0002}aa", "\U{0004}\0a");
}
method {:test} Test22() {
var r0 := isPrefix("\U{000C}\U{0008}a\U{0002}aa\0aa\U{0004}\U{0006}aaaaaaaaaa\na", "\U{000C}\U{0008}a\U{0002}aa\0aa\U{0004}\U{0006}aaaaaaaaaa\na");
expect !r0 <==> isNotPrefixPred("\U{000C}\U{0008}a\U{0002}aa\0aa\U{0004}\U{0006}aaaaaaaaaa\na", "\U{000C}\U{0008}a\U{0002}aa\0aa\U{0004}\U{0006}aaaaaaaaaa\na");
expect r0 <==> isPrefixPred("\U{000C}\U{0008}a\U{0002}aa\0aa\U{0004}\U{0006}aaaaaaaaaa\na", "\U{000C}\U{0008}a\U{0002}aa\0aa\U{0004}\U{0006}aaaaaaaaaa\na");
}
method {:test} Test23() {
var r0 := isSubstring("\U{0008}\U{0002}aaaaaaaaaaaa", "\U{0006}aa\0aaaaaaa\U{0004}aaaa\U{0008}\U{0002}aaaaaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0008}\U{0002}aaaaaaaaaaaa", "\U{0006}aa\0aaaaaaa\U{0004}aaaa\U{0008}\U{0002}aaaaaaaaaaaa");
}
method {:test} Test24() {
var r0 := isSubstring("\na\0\U{0004}", "\U{0008}\U{0002}aaaaaaaaa\U{0006}");
expect r0 <==> isSubstringPred("\na\0\U{0004}", "\U{0008}\U{0002}aaaaaaaaa\U{0006}");
}
method {:test} Test25() {
var r0 := haveCommonKSubstring(22, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(22, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}", "\U{0002}\0aaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test26() {
var r0 := haveCommonKSubstring(41, "\U{0008}a\U{0002}aaaaa\U{0006}", "\U{0004}\0");
expect r0 <==> haveCommonKSubstringPred(41, "\U{0008}a\U{0002}aaaaa\U{0006}", "\U{0004}\0");
}
method {:test} Test27() {
expect |"aaaa"| <= |"\0aaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaa", "\0aaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaa"| ==> !haveCommonKSubstringPred(k, "aaaa", "\0aaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaa", "\0aaaaaaaaaa");
}

// REPEAT 4 - TIME: 23.2643823 s

method {:test} Test28() {
var r0 := isPrefix("\U{0006}a\U{0002}a", "\U{0004}\0");
expect !r0 <==> isNotPrefixPred("\U{0006}a\U{0002}a", "\U{0004}\0");
expect r0 <==> isPrefixPred("\U{0006}a\U{0002}a", "\U{0004}\0");
}
method {:test} Test29() {
var r0 := isPrefix("\U{000E}\U{0002}aa\U{0006}aa\U{0004}a\U{0008}a\naaaaaa", "\U{000E}\U{0002}aa\U{0006}aa\U{0004}a\U{0008}a\naaaaaaaaaa\0\U{000C}");
expect !r0 <==> isNotPrefixPred("\U{000E}\U{0002}aa\U{0006}aa\U{0004}a\U{0008}a\naaaaaa", "\U{000E}\U{0002}aa\U{0006}aa\U{0004}a\U{0008}a\naaaaaaaaaa\0\U{000C}");
expect r0 <==> isPrefixPred("\U{000E}\U{0002}aa\U{0006}aa\U{0004}a\U{0008}a\naaaaaa", "\U{000E}\U{0002}aa\U{0006}aa\U{0004}a\U{0008}a\naaaaaaaaaa\0\U{000C}");
}
method {:test} Test30() {
var r0 := isSubstring("\U{0006}\U{0004}aaa\U{0002}aaaaaaaaa", "\U{0008}aaaaaaaaa\0aa\U{0006}\U{0004}aaa\U{0002}aaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0006}\U{0004}aaa\U{0002}aaaaaaaaa", "\U{0008}aaaaaaaaa\0aa\U{0006}\U{0004}aaa\U{0002}aaaaaaaaa");
}
method {:test} Test31() {
var r0 := isSubstring("\n\U{0004}aa\U{0006}", "\U{000C}\U{0002}aaaaaaa\0a\U{0008}a");
expect r0 <==> isSubstringPred("\n\U{0004}aa\U{0006}", "\U{000C}\U{0002}aaaaaaa\0a\U{0008}a");
}
method {:test} Test32() {
var r0 := haveCommonKSubstring(23, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(23, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test33() {
var r0 := haveCommonKSubstring(42, "\U{0006}\0", "\U{0004}\U{0002}a");
expect r0 <==> haveCommonKSubstringPred(42, "\U{0006}\0", "\U{0004}\U{0002}a");
}
method {:test} Test34() {
expect |"\U{0002}aaa\0"| <= |"\U{0004}aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aaa\0", "\U{0004}aaaa");
expect forall k :: r0 < k <= |"\U{0002}aaa\0"| ==> !haveCommonKSubstringPred(k, "\U{0002}aaa\0", "\U{0004}aaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aaa\0", "\U{0004}aaaa");
}

// REPEAT 5 - TIME: 28.1446058 s

method {:test} Test35() {
var r0 := isPrefix("\naaaaaaaaa\U{0002}\U{0004}aaaaaa\U{0006}aa\U{0008}aaa", "\U{000C}\0aa");
expect !r0 <==> isNotPrefixPred("\naaaaaaaaa\U{0002}\U{0004}aaaaaa\U{0006}aa\U{0008}aaa", "\U{000C}\0aa");
expect r0 <==> isPrefixPred("\naaaaaaaaa\U{0002}\U{0004}aaaaaa\U{0006}aa\U{0008}aaa", "\U{000C}\0aa");
}
method {:test} Test36() {
var r0 := isPrefix("\U{0008}\U{0002}\U{0004}a\0aaaaaa\U{0006}", "\U{0008}\U{0002}\U{0004}a\0aaaaaa\U{0006}");
expect !r0 <==> isNotPrefixPred("\U{0008}\U{0002}\U{0004}a\0aaaaaa\U{0006}", "\U{0008}\U{0002}\U{0004}a\0aaaaaa\U{0006}");
expect r0 <==> isPrefixPred("\U{0008}\U{0002}\U{0004}a\0aaaaaa\U{0006}", "\U{0008}\U{0002}\U{0004}a\0aaaaaa\U{0006}");
}
method {:test} Test37() {
var r0 := isSubstring("\U{0006}\U{0002}a", "\U{0008}\U{0004}aaaaa\0\U{0006}\U{0002}a");
expect r0 <==> isSubstringPred("\U{0006}\U{0002}a", "\U{0008}\U{0004}aaaaa\0\U{0006}\U{0002}a");
}
method {:test} Test38() {
var r0 := isSubstring("\U{0002}\0aa\U{0004}\U{0006}", "\U{000C}aaaaaaaaaa\U{0008}a\n");
expect r0 <==> isSubstringPred("\U{0002}\0aa\U{0004}\U{0006}", "\U{000C}aaaaaaaaaa\U{0008}a\n");
}
method {:test} Test39() {
var r0 := haveCommonKSubstring(24, "\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n\U{0008}\U{000C}", "\U{000E}\0\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(24, "\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\n\U{0008}\U{000C}", "\U{000E}\0\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test40() {
var r0 := haveCommonKSubstring(43, "\U{000E}aaaaaaaaaaa\U{0008}\naaaa\U{0002}aaa\U{0006}aaaaaa", "\U{000C}\0a\U{0004}");
expect r0 <==> haveCommonKSubstringPred(43, "\U{000E}aaaaaaaaaaa\U{0008}\naaaa\U{0002}aaa\U{0006}aaaaaa", "\U{000C}\0a\U{0004}");
}
method {:test} Test41() {
expect |"\0a"| <= |"\U{0002}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0a", "\U{0002}aaaaaaaa");
expect forall k :: r0 < k <= |"\0a"| ==> !haveCommonKSubstringPred(k, "\0a", "\U{0002}aaaaaaaa");
expect haveCommonKSubstringPred(r0, "\0a", "\U{0002}aaaaaaaa");
}

// REPEAT 6 - TIME: 33.622632 s

method {:test} Test42() {
var r0 := isPrefix("\U{0004}aa\0a", "\U{0002}aa");
expect !r0 <==> isNotPrefixPred("\U{0004}aa\0a", "\U{0002}aa");
expect r0 <==> isPrefixPred("\U{0004}aa\0a", "\U{0002}aa");
}
method {:test} Test43() {
var r0 := isPrefix("\U{0010}\U{0002}aa\0aa\U{0004}a\U{0006}a\U{0008}aa\naa\U{000C}\U{000E}", "\U{0010}\U{0002}aa\0aa\U{0004}a\U{0006}a\U{0008}aa\naa\U{000C}\U{000E}");
expect !r0 <==> isNotPrefixPred("\U{0010}\U{0002}aa\0aa\U{0004}a\U{0006}a\U{0008}aa\naa\U{000C}\U{000E}", "\U{0010}\U{0002}aa\0aa\U{0004}a\U{0006}a\U{0008}aa\naa\U{000C}\U{000E}");
expect r0 <==> isPrefixPred("\U{0010}\U{0002}aa\0aa\U{0004}a\U{0006}a\U{0008}aa\naa\U{000C}\U{000E}", "\U{0010}\U{0002}aa\0aa\U{0004}a\U{0006}a\U{0008}aa\naa\U{000C}\U{000E}");
}
method {:test} Test44() {
var r0 := isSubstring("\U{0006}\U{000C}\U{0004}\U{0008}", "\n\0aaa\U{0002}\U{0006}\U{000C}\U{0004}\U{0008}");
expect r0 <==> isSubstringPred("\U{0006}\U{000C}\U{0004}\U{0008}", "\n\0aaa\U{0002}\U{0006}\U{000C}\U{0004}\U{0008}");
}
method {:test} Test45() {
var r0 := isSubstring("aa\U{0004}a\U{0006}\0a", "\U{0010}\U{0002}aaaaaaaaa\U{0008}aa\U{000C}aaaaaaaaaaa\U{000E}a\n");
expect r0 <==> isSubstringPred("aa\U{0004}a\U{0006}\0a", "\U{0010}\U{0002}aaaaaaaaa\U{0008}aa\U{000C}aaaaaaaaaaa\U{000E}a\n");
}
method {:test} Test46() {
var r0 := haveCommonKSubstring(25, "\U{0012}a\U{0004}aaaaaa\naa\U{0008}aaaaaaaaaaaaa\U{000C}a", "\U{0010}\0a\U{0002}\U{0006}aaaaaaaaaaaaaaa\U{000E}aaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(25, "\U{0012}a\U{0004}aaaaaa\naa\U{0008}aaaaaaaaaaaaa\U{000C}a", "\U{0010}\0a\U{0002}\U{0006}aaaaaaaaaaaaaaa\U{000E}aaaaaaaaa");
}
method {:test} Test47() {
var r0 := haveCommonKSubstring(44, "\U{0006}aaaaaa\U{0002}aa", "\U{0004}\0a");
expect r0 <==> haveCommonKSubstringPred(44, "\U{0006}aaaaaa\U{0002}aa", "\U{0004}\0a");
}
method {:test} Test48() {
expect |"\0aa"| <= |"\U{0002}aaaaaa\U{0004}aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0aa", "\U{0002}aaaaaa\U{0004}aaaa");
expect forall k :: r0 < k <= |"\0aa"| ==> !haveCommonKSubstringPred(k, "\0aa", "\U{0002}aaaaaa\U{0004}aaaa");
expect haveCommonKSubstringPred(r0, "\0aa", "\U{0002}aaaaaa\U{0004}aaaa");
}

// REPEAT 7 - TIME: 39.6583938 s

method {:test} Test49() {
var r0 := isPrefix("\U{0008}a\U{0004}aa", "\U{0006}\U{0002}\0a");
expect !r0 <==> isNotPrefixPred("\U{0008}a\U{0004}aa", "\U{0006}\U{0002}\0a");
expect r0 <==> isPrefixPred("\U{0008}a\U{0004}aa", "\U{0006}\U{0002}\0a");
}
method {:test} Test50() {
var r0 := isPrefix("\U{000E}\0aaa\U{0004}aaa\U{0002}a\U{0008}aa\na\U{0006}a\U{000C}aa", "\U{000E}\0aaa\U{0004}aaa\U{0002}a\U{0008}aa\na\U{0006}a\U{000C}aa");
expect !r0 <==> isNotPrefixPred("\U{000E}\0aaa\U{0004}aaa\U{0002}a\U{0008}aa\na\U{0006}a\U{000C}aa", "\U{000E}\0aaa\U{0004}aaa\U{0002}a\U{0008}aa\na\U{0006}a\U{000C}aa");
expect r0 <==> isPrefixPred("\U{000E}\0aaa\U{0004}aaa\U{0002}a\U{0008}aa\na\U{0006}a\U{000C}aa", "\U{000E}\0aaa\U{0004}aaa\U{0002}a\U{0008}aa\na\U{0006}a\U{000C}aa");
}
method {:test} Test51() {
var r0 := isSubstring("\U{0006}\U{0004}aaa\U{0008}", "\n\U{0002}aa\0a\U{0006}\U{0004}aaa\U{0008}");
expect r0 <==> isSubstringPred("\U{0006}\U{0004}aaa\U{0008}", "\n\U{0002}aa\0a\U{0006}\U{0004}aaa\U{0008}");
}
method {:test} Test52() {
var r0 := isSubstring("\U{0004}aa\U{0002}a\0a\naaaaa\U{0006}\U{0008}a", "\U{0018}aaaaaaaaaa\U{000E}a\U{0012}aaaaaa\U{0014}a\U{000C}a\U{0010}a\U{0016}");
expect r0 <==> isSubstringPred("\U{0004}aa\U{0002}a\0a\naaaaa\U{0006}\U{0008}a", "\U{0018}aaaaaaaaaa\U{000E}a\U{0012}aaaaaa\U{0014}a\U{000C}a\U{0010}a\U{0016}");
}
method {:test} Test53() {
var r0 := haveCommonKSubstring(26, "\U{0010}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{0004}", "\U{000E}\0\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0008}aa\naa");
expect r0 <==> haveCommonKSubstringPred(26, "\U{0010}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\U{0004}", "\U{000E}\0\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0008}aa\naa");
}
method {:test} Test54() {
var r0 := haveCommonKSubstring(45, "\U{0006}aaaaaa\U{0008}a\U{0002}aaaa", "\n\U{0004}aaa\0aaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(45, "\U{0006}aaaaaa\U{0008}a\U{0002}aaaa", "\n\U{0004}aaa\0aaaaaaaaa");
}
method {:test} Test55() {
expect |"\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa"| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa");
expect forall k :: r0 < k <= |"\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa");
}

// REPEAT 8 - TIME: 45.9518014 s

method {:test} Test56() {
var r0 := isPrefix("\naa\U{0002}aaaaaaaaaaaaaaaaa", "\U{0008}\0a\U{0004}\U{0006}");
expect !r0 <==> isNotPrefixPred("\naa\U{0002}aaaaaaaaaaaaaaaaa", "\U{0008}\0a\U{0004}\U{0006}");
expect r0 <==> isPrefixPred("\naa\U{0002}aaaaaaaaaaaaaaaaa", "\U{0008}\0a\U{0004}\U{0006}");
}
method {:test} Test57() {
var r0 := isPrefix("\U{0016}\U{0002}aaa\U{0008}aaaa\0aaaa\U{0006}aa\U{000E}\U{0010}\U{000C}\U{0004}\U{0014}\n\U{0012}a", "\U{0016}\U{0002}aaa\U{0008}aaaa\0aaaa\U{0006}aa\U{000E}\U{0010}\U{000C}\U{0004}\U{0014}\n\U{0012}a");
expect !r0 <==> isNotPrefixPred("\U{0016}\U{0002}aaa\U{0008}aaaa\0aaaa\U{0006}aa\U{000E}\U{0010}\U{000C}\U{0004}\U{0014}\n\U{0012}a", "\U{0016}\U{0002}aaa\U{0008}aaaa\0aaaa\U{0006}aa\U{000E}\U{0010}\U{000C}\U{0004}\U{0014}\n\U{0012}a");
expect r0 <==> isPrefixPred("\U{0016}\U{0002}aaa\U{0008}aaaa\0aaaa\U{0006}aa\U{000E}\U{0010}\U{000C}\U{0004}\U{0014}\n\U{0012}a", "\U{0016}\U{0002}aaa\U{0008}aaaa\0aaaa\U{0006}aa\U{000E}\U{0010}\U{000C}\U{0004}\U{0014}\n\U{0012}a");
}
method {:test} Test58() {
var r0 := isSubstring("\U{0004}\U{0006}\U{0002}aa", "\U{0008}\0\U{0004}\U{0006}\U{0002}aaaaaa");
expect r0 <==> isSubstringPred("\U{0004}\U{0006}\U{0002}aa", "\U{0008}\0\U{0004}\U{0006}\U{0002}aaaaaa");
}
method {:test} Test59() {
var r0 := isSubstring("\U{0004}aa\U{0002}", "\U{0006}\0");
expect r0 <==> isSubstringPred("\U{0004}aa\U{0002}", "\U{0006}\0");
}
method {:test} Test60() {
var r0 := haveCommonKSubstring(27, "\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{000E}", "\U{0010}\0\U{0002}aaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}a\n\U{000C}");
expect r0 <==> haveCommonKSubstringPred(27, "\U{0012}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\U{000E}", "\U{0010}\0\U{0002}aaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}a\n\U{000C}");
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(46, "\0aaaaaaa\U{0002}", "\U{0006}\U{0004}a");
expect r0 <==> haveCommonKSubstringPred(46, "\0aaaaaaa\U{0002}", "\U{0006}\U{0004}a");
}
method {:test} Test62() {
expect |"\U{0004}aaaaa\0"| <= |"\U{0006}aaaa\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaa\0", "\U{0006}aaaa\U{0002}aa");
expect forall k :: r0 < k <= |"\U{0004}aaaaa\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaa\0", "\U{0006}aaaa\U{0002}aa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaa\0", "\U{0006}aaaa\U{0002}aa");
}

// REPEAT 9 - TIME: 52.7022165 s

method {:test} Test63() {
var r0 := isPrefix("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aa\0aa");
expect !r0 <==> isNotPrefixPred("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aa\0aa");
expect r0 <==> isPrefixPred("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aa\0aa");
}
method {:test} Test64() {
var r0 := isPrefix("\U{0018}aaa\U{0002}\U{0008}aaa\U{0004}a\n\U{0006}aa\0aaa\U{000C}\U{0010}\U{0012}a\U{000E}\U{0016}\U{0014}", "\U{0018}aaa\U{0002}\U{0008}aaa\U{0004}a\n\U{0006}aa\0aaa\U{000C}\U{0010}\U{0012}a\U{000E}\U{0016}\U{0014}");
expect !r0 <==> isNotPrefixPred("\U{0018}aaa\U{0002}\U{0008}aaa\U{0004}a\n\U{0006}aa\0aaa\U{000C}\U{0010}\U{0012}a\U{000E}\U{0016}\U{0014}", "\U{0018}aaa\U{0002}\U{0008}aaa\U{0004}a\n\U{0006}aa\0aaa\U{000C}\U{0010}\U{0012}a\U{000E}\U{0016}\U{0014}");
expect r0 <==> isPrefixPred("\U{0018}aaa\U{0002}\U{0008}aaa\U{0004}a\n\U{0006}aa\0aaa\U{000C}\U{0010}\U{0012}a\U{000E}\U{0016}\U{0014}", "\U{0018}aaa\U{0002}\U{0008}aaa\U{0004}a\n\U{0006}aa\0aaa\U{000C}\U{0010}\U{0012}a\U{000E}\U{0016}\U{0014}");
}
method {:test} Test65() {
var r0 := isSubstring("\U{0008}\U{0002}a\U{0006}", "\n\U{0004}aaa\0\U{0008}\U{0002}a\U{0006}aa");
expect r0 <==> isSubstringPred("\U{0008}\U{0002}a\U{0006}", "\n\U{0004}aaa\0\U{0008}\U{0002}a\U{0006}aa");
}
method {:test} Test66() {
var r0 := isSubstring("\U{0002}aaaaaaaaa", "\0aa");
expect r0 <==> isSubstringPred("\U{0002}aaaaaaaaa", "\0aa");
}
method {:test} Test67() {
var r0 := haveCommonKSubstring(28, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(28, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test68() {
var r0 := haveCommonKSubstring(47, "\U{0010}aaaaaaaa\U{0004}\U{0006}aaa\U{0008}", "\U{0012}aaaaaaaaaa\0aaa\naaaaaaaaaaa\U{0002}\U{000C}\U{000E}");
expect r0 <==> haveCommonKSubstringPred(47, "\U{0010}aaaaaaaa\U{0004}\U{0006}aaa\U{0008}", "\U{0012}aaaaaaaaaa\0aaa\naaaaaaaaaaa\U{0002}\U{000C}\U{000E}");
}
method {:test} Test69() {
expect |"\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 10 - TIME: 59.1861252 s

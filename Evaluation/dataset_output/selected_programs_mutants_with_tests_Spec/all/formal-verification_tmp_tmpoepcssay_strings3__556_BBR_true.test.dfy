// formal-verification_tmp_tmpoepcssay_strings3.dfy

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
  ensures res ==> isSubstringPred(sub, str)
  ensures isSubstringPred(sub, str) ==> res
  ensures isSubstringPred(sub, str) ==> res
  ensures !res <==> isNotSubstringPred(sub, str)
{
  if |str| < |sub| {
    return false;
  } else {
    var i: nat := 0;
    res := false;
    while i <= |str| - |sub| && res == false
      invariant 0 <= i <= |str| - |sub| + 1
      invariant res ==> isSubstringPred(sub, str)
      invariant forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
      decreases |str| - |sub| - i + if !res then 1 else 0
    {
      res := isPrefix(sub, str[i..]);
      if !res {
        i := i + 1;
      }
    }
  }
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
  ensures !found <==> haveNotCommonKSubstringPred(k, str1, str2)
{
  if k <= |str1| && k <= |str2| {
    var slice: string;
    found := false;
    var i: nat := 0;
    while i <= |str1| - k && found == false
      invariant found ==> haveCommonKSubstringPred(k, str1, str2)
      invariant forall x, y :: 0 <= x < i && found == false && y == x + k && y <= |str1| ==> isNotSubstringPred(str1[x .. y], str2)
      decreases |str1| - k - i + if !found then 1 else 0
    {
      slice := str1[i .. i + k];
      found := isSubstring(slice, str2);
      i := i + 1;
    }
  } else {
    return false;
  }
}

method {:testEntry} maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  requires |str1| <= |str2|
  ensures forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
  ensures haveCommonKSubstringPred(len, str1, str2)
{
  assert isPrefixPred(str1[0 .. 0], str2[0..]);
  len := |str1|;
  var hasCommon: bool := true;
  while len > 0
    invariant forall i :: len < i <= |str1| ==> !haveCommonKSubstringPred(i, str1, str2)
    decreases len
  {
    hasCommon := haveCommonKSubstring(len, str1, str2);
    if hasCommon {
      return len;
    }
    len := len - 1;
  }
  return len;
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
var r0 := isSubstring("aaaaaaaaaaa", "aaaaaaaaaaaa");
expect r0 <==> isSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa");
expect r0 ==> isSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa");
expect isSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa") ==> r0;
expect isSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa");
}
method {:test} Test3() {
var r0 := isSubstring("", "");
expect r0 <==> isSubstringPred("", "");
expect r0 ==> isSubstringPred("", "");
expect isSubstringPred("", "") ==> r0;
expect isSubstringPred("", "") ==> r0;
expect !r0 <==> isNotSubstringPred("", "");
}
method {:test} Test4() {
var r0 := haveCommonKSubstring(21, "aaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(21, "aaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(21, "aaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test5() {
var r0 := haveCommonKSubstring(38, "", "");
expect r0 <==> haveCommonKSubstringPred(38, "", "");
expect !r0 <==> haveNotCommonKSubstringPred(38, "", "");
}
method {:test} Test6() {
expect |"aaaaaa"| <= |"aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaa", "aaaaaaa");
expect forall k :: r0 < k <= |"aaaaaa"| ==> !haveCommonKSubstringPred(k, "aaaaaa", "aaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaa", "aaaaaaa");
}

// REPEAT 1 - TIME: 12.7255441 s

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
var r0 := isSubstring("aaaaa\0aaaaaaaaaaa\U{0002}", "aaaaaaaaaaa\0aaaaa\0aaaaa\U{0002}aaaaa\U{0002}");
expect r0 <==> isSubstringPred("aaaaa\0aaaaaaaaaaa\U{0002}", "aaaaaaaaaaa\0aaaaa\0aaaaa\U{0002}aaaaa\U{0002}");
expect r0 ==> isSubstringPred("aaaaa\0aaaaaaaaaaa\U{0002}", "aaaaaaaaaaa\0aaaaa\0aaaaa\U{0002}aaaaa\U{0002}");
expect isSubstringPred("aaaaa\0aaaaaaaaaaa\U{0002}", "aaaaaaaaaaa\0aaaaa\0aaaaa\U{0002}aaaaa\U{0002}") ==> r0;
expect isSubstringPred("aaaaa\0aaaaaaaaaaa\U{0002}", "aaaaaaaaaaa\0aaaaa\0aaaaa\U{0002}aaaaa\U{0002}") ==> r0;
expect !r0 <==> isNotSubstringPred("aaaaa\0aaaaaaaaaaa\U{0002}", "aaaaaaaaaaa\0aaaaa\0aaaaa\U{0002}aaaaa\U{0002}");
}
method {:test} Test10() {
var r0 := isSubstring("aaa\0aaaaaaa\U{0004}", "aaaaaaaa\U{0002}");
expect r0 <==> isSubstringPred("aaa\0aaaaaaa\U{0004}", "aaaaaaaa\U{0002}");
expect r0 ==> isSubstringPred("aaa\0aaaaaaa\U{0004}", "aaaaaaaa\U{0002}");
expect isSubstringPred("aaa\0aaaaaaa\U{0004}", "aaaaaaaa\U{0002}") ==> r0;
expect isSubstringPred("aaa\0aaaaaaa\U{0004}", "aaaaaaaa\U{0002}") ==> r0;
expect !r0 <==> isNotSubstringPred("aaa\0aaaaaaa\U{0004}", "aaaaaaaa\U{0002}");
}
method {:test} Test11() {
var r0 := haveCommonKSubstring(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test12() {
var r0 := haveCommonKSubstring(39, "\U{0002}", "aaaaaaaaaaaaaaaaaaa\0aaaaa");
expect r0 <==> haveCommonKSubstringPred(39, "\U{0002}", "aaaaaaaaaaaaaaaaaaa\0aaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(39, "\U{0002}", "aaaaaaaaaaaaaaaaaaa\0aaaaa");
}
method {:test} Test13() {
expect |"aaaaaa\0"| <= |"aaaaaaa\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaa\0", "aaaaaaa\U{0002}a");
expect forall k :: r0 < k <= |"aaaaaa\0"| ==> !haveCommonKSubstringPred(k, "aaaaaa\0", "aaaaaaa\U{0002}a");
expect haveCommonKSubstringPred(r0, "aaaaaa\0", "aaaaaaa\U{0002}a");
}

// REPEAT 2 - TIME: 20.6657279 s

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
var r0 := isSubstring("\0", "\U{0002}aaaaaaa\0aaaaaaaaaaa\0");
expect r0 <==> isSubstringPred("\0", "\U{0002}aaaaaaa\0aaaaaaaaaaa\0");
expect r0 ==> isSubstringPred("\0", "\U{0002}aaaaaaa\0aaaaaaaaaaa\0");
expect isSubstringPred("\0", "\U{0002}aaaaaaa\0aaaaaaaaaaa\0") ==> r0;
expect isSubstringPred("\0", "\U{0002}aaaaaaa\0aaaaaaaaaaa\0") ==> r0;
expect !r0 <==> isNotSubstringPred("\0", "\U{0002}aaaaaaa\0aaaaaaaaaaa\0");
}
method {:test} Test17() {
var r0 := isSubstring("a", "\0");
expect r0 <==> isSubstringPred("a", "\0");
expect r0 ==> isSubstringPred("a", "\0");
expect isSubstringPred("a", "\0") ==> r0;
expect isSubstringPred("a", "\0") ==> r0;
expect !r0 <==> isNotSubstringPred("a", "\0");
}
method {:test} Test18() {
var r0 := haveCommonKSubstring(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test19() {
var r0 := haveCommonKSubstring(40, "\n\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> haveCommonKSubstringPred(40, "\n\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect !r0 <==> haveNotCommonKSubstringPred(40, "\n\U{0004}aaaaaaa\U{0002}aaaaaaaaaaaa\U{0006}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
}
method {:test} Test20() {
expect |"aaaaaaa\0"| <= |"\U{0002}aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaaaaa\0", "\U{0002}aaaaaaa");
expect forall k :: r0 < k <= |"aaaaaaa\0"| ==> !haveCommonKSubstringPred(k, "aaaaaaa\0", "\U{0002}aaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaaaaa\0", "\U{0002}aaaaaaa");
}

// REPEAT 3 - TIME: 28.4095483 s

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
var r0 := isSubstring("\U{0006}a\0\U{0002}", "\U{0008}aaaaaaaa\U{0004}\U{0006}a\0\U{0002}\U{0006}a\0\U{0002}");
expect r0 <==> isSubstringPred("\U{0006}a\0\U{0002}", "\U{0008}aaaaaaaa\U{0004}\U{0006}a\0\U{0002}\U{0006}a\0\U{0002}");
expect r0 ==> isSubstringPred("\U{0006}a\0\U{0002}", "\U{0008}aaaaaaaa\U{0004}\U{0006}a\0\U{0002}\U{0006}a\0\U{0002}");
expect isSubstringPred("\U{0006}a\0\U{0002}", "\U{0008}aaaaaaaa\U{0004}\U{0006}a\0\U{0002}\U{0006}a\0\U{0002}") ==> r0;
expect isSubstringPred("\U{0006}a\0\U{0002}", "\U{0008}aaaaaaaa\U{0004}\U{0006}a\0\U{0002}\U{0006}a\0\U{0002}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0006}a\0\U{0002}", "\U{0008}aaaaaaaa\U{0004}\U{0006}a\0\U{0002}\U{0006}a\0\U{0002}");
}
method {:test} Test24() {
var r0 := isSubstring("a\U{0002}\U{0006}aa\0aaaaa\U{0008}\naaaaa\U{000C}", "\U{000E}aa\U{0004}aaaaaa");
expect r0 <==> isSubstringPred("a\U{0002}\U{0006}aa\0aaaaa\U{0008}\naaaaa\U{000C}", "\U{000E}aa\U{0004}aaaaaa");
expect r0 ==> isSubstringPred("a\U{0002}\U{0006}aa\0aaaaa\U{0008}\naaaaa\U{000C}", "\U{000E}aa\U{0004}aaaaaa");
expect isSubstringPred("a\U{0002}\U{0006}aa\0aaaaa\U{0008}\naaaaa\U{000C}", "\U{000E}aa\U{0004}aaaaaa") ==> r0;
expect isSubstringPred("a\U{0002}\U{0006}aa\0aaaaa\U{0008}\naaaaa\U{000C}", "\U{000E}aa\U{0004}aaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("a\U{0002}\U{0006}aa\0aaaaa\U{0008}\naaaaa\U{000C}", "\U{000E}aa\U{0004}aaaaaa");
}
method {:test} Test25() {
var r0 := haveCommonKSubstring(24, "\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> haveCommonKSubstringPred(24, "\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect !r0 <==> haveNotCommonKSubstringPred(24, "\0aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa\U{0006}");
}
method {:test} Test26() {
var r0 := haveCommonKSubstring(41, "a\U{0002}aaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0006}a", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\n\U{000C}\U{000E}");
expect r0 <==> haveCommonKSubstringPred(41, "a\U{0002}aaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0006}a", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\n\U{000C}\U{000E}");
expect !r0 <==> haveNotCommonKSubstringPred(41, "a\U{0002}aaaaaaaaaaa\0aaaaaaaa\U{0004}\U{0006}a", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}\n\U{000C}\U{000E}");
}
method {:test} Test27() {
expect |"aaaa"| <= |"\0aaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("aaaa", "\0aaaaaaaaaa");
expect forall k :: r0 < k <= |"aaaa"| ==> !haveCommonKSubstringPred(k, "aaaa", "\0aaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "aaaa", "\0aaaaaaaaaa");
}

// REPEAT 4 - TIME: 36.1723952 s

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
var r0 := isSubstring("\U{0002}\U{0006}", "\U{0004}\0aaaa\U{0002}\U{0006}a\U{0002}\U{0006}");
expect r0 <==> isSubstringPred("\U{0002}\U{0006}", "\U{0004}\0aaaa\U{0002}\U{0006}a\U{0002}\U{0006}");
expect r0 ==> isSubstringPred("\U{0002}\U{0006}", "\U{0004}\0aaaa\U{0002}\U{0006}a\U{0002}\U{0006}");
expect isSubstringPred("\U{0002}\U{0006}", "\U{0004}\0aaaa\U{0002}\U{0006}a\U{0002}\U{0006}") ==> r0;
expect isSubstringPred("\U{0002}\U{0006}", "\U{0004}\0aaaa\U{0002}\U{0006}a\U{0002}\U{0006}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0002}\U{0006}", "\U{0004}\0aaaa\U{0002}\U{0006}a\U{0002}\U{0006}");
}
method {:test} Test31() {
var r0 := isSubstring("\na\U{0002}a\U{0004}", "\U{000C}aaaaaaa\0\U{0006}\U{0008}");
expect r0 <==> isSubstringPred("\na\U{0002}a\U{0004}", "\U{000C}aaaaaaa\0\U{0006}\U{0008}");
expect r0 ==> isSubstringPred("\na\U{0002}a\U{0004}", "\U{000C}aaaaaaa\0\U{0006}\U{0008}");
expect isSubstringPred("\na\U{0002}a\U{0004}", "\U{000C}aaaaaaa\0\U{0006}\U{0008}") ==> r0;
expect isSubstringPred("\na\U{0002}a\U{0004}", "\U{000C}aaaaaaa\0\U{0006}\U{0008}") ==> r0;
expect !r0 <==> isNotSubstringPred("\na\U{0002}a\U{0004}", "\U{000C}aaaaaaa\0\U{0006}\U{0008}");
}
method {:test} Test32() {
var r0 := haveCommonKSubstring(25, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "a\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}a\U{0004}");
expect r0 <==> haveCommonKSubstringPred(25, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "a\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}a\U{0004}");
expect !r0 <==> haveNotCommonKSubstringPred(25, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "a\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}a\U{0006}a\U{0004}");
}
method {:test} Test33() {
var r0 := haveCommonKSubstring(42, "\U{000E}\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaa", "\U{000C}aaaaaaaaaaaaaaaaaaaaa\0a\n\U{0008}");
expect r0 <==> haveCommonKSubstringPred(42, "\U{000E}\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaa", "\U{000C}aaaaaaaaaaaaaaaaaaaaa\0a\n\U{0008}");
expect !r0 <==> haveNotCommonKSubstringPred(42, "\U{000E}\U{0002}aaaaaaaaaaaaaaaaaaaa\U{0004}\U{0006}aaaaa", "\U{000C}aaaaaaaaaaaaaaaaaaaaa\0a\n\U{0008}");
}
method {:test} Test34() {
expect |"\U{0002}aaa\0"| <= |"\U{0004}aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aaa\0", "\U{0004}aaaa");
expect forall k :: r0 < k <= |"\U{0002}aaa\0"| ==> !haveCommonKSubstringPred(k, "\U{0002}aaa\0", "\U{0004}aaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aaa\0", "\U{0004}aaaa");
}

// REPEAT 5 - TIME: 44.4833925 s

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
var r0 := isSubstring("\n\U{0002}\U{0008}", "\U{000C}aaaaaaaa\U{0004}aa\U{0006}aaaa\0aaa\U{000E}\n\U{0002}\U{0008}\n\U{0002}\U{0008}");
expect r0 <==> isSubstringPred("\n\U{0002}\U{0008}", "\U{000C}aaaaaaaa\U{0004}aa\U{0006}aaaa\0aaa\U{000E}\n\U{0002}\U{0008}\n\U{0002}\U{0008}");
expect r0 ==> isSubstringPred("\n\U{0002}\U{0008}", "\U{000C}aaaaaaaa\U{0004}aa\U{0006}aaaa\0aaa\U{000E}\n\U{0002}\U{0008}\n\U{0002}\U{0008}");
expect isSubstringPred("\n\U{0002}\U{0008}", "\U{000C}aaaaaaaa\U{0004}aa\U{0006}aaaa\0aaa\U{000E}\n\U{0002}\U{0008}\n\U{0002}\U{0008}") ==> r0;
expect isSubstringPred("\n\U{0002}\U{0008}", "\U{000C}aaaaaaaa\U{0004}aa\U{0006}aaaa\0aaa\U{000E}\n\U{0002}\U{0008}\n\U{0002}\U{0008}") ==> r0;
expect !r0 <==> isNotSubstringPred("\n\U{0002}\U{0008}", "\U{000C}aaaaaaaa\U{0004}aa\U{0006}aaaa\0aaa\U{000E}\n\U{0002}\U{0008}\n\U{0002}\U{0008}");
}
method {:test} Test38() {
var r0 := isSubstring("\U{0004}\0", "\U{0006}\U{0002}");
expect r0 <==> isSubstringPred("\U{0004}\0", "\U{0006}\U{0002}");
expect r0 ==> isSubstringPred("\U{0004}\0", "\U{0006}\U{0002}");
expect isSubstringPred("\U{0004}\0", "\U{0006}\U{0002}") ==> r0;
expect isSubstringPred("\U{0004}\0", "\U{0006}\U{0002}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}\0", "\U{0006}\U{0002}");
}
method {:test} Test39() {
var r0 := haveCommonKSubstring(26, "\naaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0004}aa", "\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect r0 <==> haveCommonKSubstringPred(26, "\naaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0004}aa", "\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect !r0 <==> haveNotCommonKSubstringPred(26, "\naaaaaaaaaaaaaaaaaaaaaa\0\U{0002}\U{0004}aa", "\U{0006}\U{0008}aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
}
method {:test} Test40() {
var r0 := haveCommonKSubstring(43, "\U{0016}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0008}a\U{000C}", "\U{0014}aaaaaaaaaaaaaaaaaaaaaa\0\na\U{0010}\U{000E}\U{0012}");
expect r0 <==> haveCommonKSubstringPred(43, "\U{0016}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0008}a\U{000C}", "\U{0014}aaaaaaaaaaaaaaaaaaaaaa\0\na\U{0010}\U{000E}\U{0012}");
expect !r0 <==> haveNotCommonKSubstringPred(43, "\U{0016}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}aa\U{0006}\U{0008}a\U{000C}", "\U{0014}aaaaaaaaaaaaaaaaaaaaaa\0\na\U{0010}\U{000E}\U{0012}");
}
method {:test} Test41() {
expect |"\0a"| <= |"\U{0002}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0a", "\U{0002}aaaaaaaa");
expect forall k :: r0 < k <= |"\0a"| ==> !haveCommonKSubstringPred(k, "\0a", "\U{0002}aaaaaaaa");
expect haveCommonKSubstringPred(r0, "\0a", "\U{0002}aaaaaaaa");
}

// REPEAT 6 - TIME: 52.6395064 s

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
var r0 := isSubstring("\0\0", "\U{0002}\0\0\0");
expect r0 <==> isSubstringPred("\0\0", "\U{0002}\0\0\0");
expect r0 ==> isSubstringPred("\0\0", "\U{0002}\0\0\0");
expect isSubstringPred("\0\0", "\U{0002}\0\0\0") ==> r0;
expect isSubstringPred("\0\0", "\U{0002}\0\0\0") ==> r0;
expect !r0 <==> isNotSubstringPred("\0\0", "\U{0002}\0\0\0");
}
method {:test} Test45() {
var r0 := isSubstring("\U{0014}aa\U{0004}\U{0006}\U{0008}", "\U{0010}\0aaaaaaaaa\U{000C}a\naa\U{000E}\U{0002}\U{0012}");
expect r0 <==> isSubstringPred("\U{0014}aa\U{0004}\U{0006}\U{0008}", "\U{0010}\0aaaaaaaaa\U{000C}a\naa\U{000E}\U{0002}\U{0012}");
expect r0 ==> isSubstringPred("\U{0014}aa\U{0004}\U{0006}\U{0008}", "\U{0010}\0aaaaaaaaa\U{000C}a\naa\U{000E}\U{0002}\U{0012}");
expect isSubstringPred("\U{0014}aa\U{0004}\U{0006}\U{0008}", "\U{0010}\0aaaaaaaaa\U{000C}a\naa\U{000E}\U{0002}\U{0012}") ==> r0;
expect isSubstringPred("\U{0014}aa\U{0004}\U{0006}\U{0008}", "\U{0010}\0aaaaaaaaa\U{000C}a\naa\U{000E}\U{0002}\U{0012}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0014}aa\U{0004}\U{0006}\U{0008}", "\U{0010}\0aaaaaaaaa\U{000C}a\naa\U{000E}\U{0002}\U{0012}");
}
method {:test} Test46() {
var r0 := haveCommonKSubstring(27, "\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(27, "\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(27, "\U{0002}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test47() {
var r0 := haveCommonKSubstring(44, "\U{0008}\U{0004}aaaaa\U{0002}aaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaa\0");
expect r0 <==> haveCommonKSubstringPred(44, "\U{0008}\U{0004}aaaaa\U{0002}aaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaa\0");
expect !r0 <==> haveNotCommonKSubstringPred(44, "\U{0008}\U{0004}aaaaa\U{0002}aaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaa\0");
}
method {:test} Test48() {
expect |"\0aa"| <= |"\U{0002}aaaaaa\U{0004}aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0aa", "\U{0002}aaaaaa\U{0004}aaaa");
expect forall k :: r0 < k <= |"\0aa"| ==> !haveCommonKSubstringPred(k, "\0aa", "\U{0002}aaaaaa\U{0004}aaaa");
expect haveCommonKSubstringPred(r0, "\0aa", "\U{0002}aaaaaa\U{0004}aaaa");
}

// REPEAT 7 - TIME: 61.6046526 s

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
var r0 := isSubstring("\U{0006}\U{0004}", "\U{0002}\0\U{0006}\U{0004}\U{0006}\U{0004}");
expect r0 <==> isSubstringPred("\U{0006}\U{0004}", "\U{0002}\0\U{0006}\U{0004}\U{0006}\U{0004}");
expect r0 ==> isSubstringPred("\U{0006}\U{0004}", "\U{0002}\0\U{0006}\U{0004}\U{0006}\U{0004}");
expect isSubstringPred("\U{0006}\U{0004}", "\U{0002}\0\U{0006}\U{0004}\U{0006}\U{0004}") ==> r0;
expect isSubstringPred("\U{0006}\U{0004}", "\U{0002}\0\U{0006}\U{0004}\U{0006}\U{0004}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0006}\U{0004}", "\U{0002}\0\U{0006}\U{0004}\U{0006}\U{0004}");
}
method {:test} Test52() {
var r0 := isSubstring("\na\U{0002}a\U{0006}aa", "\U{0008}\U{0004}\0");
expect r0 <==> isSubstringPred("\na\U{0002}a\U{0006}aa", "\U{0008}\U{0004}\0");
expect r0 ==> isSubstringPred("\na\U{0002}a\U{0006}aa", "\U{0008}\U{0004}\0");
expect isSubstringPred("\na\U{0002}a\U{0006}aa", "\U{0008}\U{0004}\0") ==> r0;
expect isSubstringPred("\na\U{0002}a\U{0006}aa", "\U{0008}\U{0004}\0") ==> r0;
expect !r0 <==> isNotSubstringPred("\na\U{0002}a\U{0006}aa", "\U{0008}\U{0004}\0");
}
method {:test} Test53() {
var r0 := haveCommonKSubstring(28, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(28, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(28, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaa\U{0006}aaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test54() {
var r0 := haveCommonKSubstring(45, "\U{0006}\U{0004}aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa", "\U{0008}aaaaaaaa\0");
expect r0 <==> haveCommonKSubstringPred(45, "\U{0006}\U{0004}aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa", "\U{0008}aaaaaaaa\0");
expect !r0 <==> haveNotCommonKSubstringPred(45, "\U{0006}\U{0004}aaaaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa", "\U{0008}aaaaaaaa\0");
}
method {:test} Test55() {
expect |"\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa"| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa");
expect forall k :: r0 < k <= |"\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aa\0aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaaaaa");
}

// REPEAT 8 - TIME: 71.7196101 s

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
var r0 := isSubstring("\U{0008}\U{0004}a", "\naaaaaaaa\0\U{0002}\U{0006}a\U{0008}\U{0004}\U{0008}\U{0004}a");
expect r0 <==> isSubstringPred("\U{0008}\U{0004}a", "\naaaaaaaa\0\U{0002}\U{0006}a\U{0008}\U{0004}\U{0008}\U{0004}a");
expect r0 ==> isSubstringPred("\U{0008}\U{0004}a", "\naaaaaaaa\0\U{0002}\U{0006}a\U{0008}\U{0004}\U{0008}\U{0004}a");
expect isSubstringPred("\U{0008}\U{0004}a", "\naaaaaaaa\0\U{0002}\U{0006}a\U{0008}\U{0004}\U{0008}\U{0004}a") ==> r0;
expect isSubstringPred("\U{0008}\U{0004}a", "\naaaaaaaa\0\U{0002}\U{0006}a\U{0008}\U{0004}\U{0008}\U{0004}a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0008}\U{0004}a", "\naaaaaaaa\0\U{0002}\U{0006}a\U{0008}\U{0004}\U{0008}\U{0004}a");
}
method {:test} Test59() {
var r0 := isSubstring("\U{000E}\0aaa\U{0008}\U{0004}\n", "\U{000C}aa\U{0002}\U{0006}");
expect r0 <==> isSubstringPred("\U{000E}\0aaa\U{0008}\U{0004}\n", "\U{000C}aa\U{0002}\U{0006}");
expect r0 ==> isSubstringPred("\U{000E}\0aaa\U{0008}\U{0004}\n", "\U{000C}aa\U{0002}\U{0006}");
expect isSubstringPred("\U{000E}\0aaa\U{0008}\U{0004}\n", "\U{000C}aa\U{0002}\U{0006}") ==> r0;
expect isSubstringPred("\U{000E}\0aaa\U{0008}\U{0004}\n", "\U{000C}aa\U{0002}\U{0006}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{000E}\0aaa\U{0008}\U{0004}\n", "\U{000C}aa\U{0002}\U{0006}");
}
method {:test} Test60() {
var r0 := haveCommonKSubstring(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(46, "\n\0aaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{000C}aaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0008}a\U{0006}");
expect r0 <==> haveCommonKSubstringPred(46, "\n\0aaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{000C}aaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0008}a\U{0006}");
expect !r0 <==> haveNotCommonKSubstringPred(46, "\n\0aaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{000C}aaaaaaaaaaaaaa\U{0002}aaaaaaaa\U{0008}a\U{0006}");
}
method {:test} Test62() {
expect |"\U{0004}aaaaa\0"| <= |"\U{0006}aaaa\U{0002}aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaa\0", "\U{0006}aaaa\U{0002}aa");
expect forall k :: r0 < k <= |"\U{0004}aaaaa\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaa\0", "\U{0006}aaaa\U{0002}aa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaa\0", "\U{0006}aaaa\U{0002}aa");
}

// REPEAT 9 - TIME: 81.0013928 s

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
var r0 := isSubstring("\U{000C}aaa\0\U{0008}aaaaa\U{0008}a", "\na\U{0002}\U{0004}aa\U{0006}a\U{000C}aaa\0\U{0008}\U{000C}aaa\0\U{0008}aaaaa\U{0008}a");
expect r0 <==> isSubstringPred("\U{000C}aaa\0\U{0008}aaaaa\U{0008}a", "\na\U{0002}\U{0004}aa\U{0006}a\U{000C}aaa\0\U{0008}\U{000C}aaa\0\U{0008}aaaaa\U{0008}a");
expect r0 ==> isSubstringPred("\U{000C}aaa\0\U{0008}aaaaa\U{0008}a", "\na\U{0002}\U{0004}aa\U{0006}a\U{000C}aaa\0\U{0008}\U{000C}aaa\0\U{0008}aaaaa\U{0008}a");
expect isSubstringPred("\U{000C}aaa\0\U{0008}aaaaa\U{0008}a", "\na\U{0002}\U{0004}aa\U{0006}a\U{000C}aaa\0\U{0008}\U{000C}aaa\0\U{0008}aaaaa\U{0008}a") ==> r0;
expect isSubstringPred("\U{000C}aaa\0\U{0008}aaaaa\U{0008}a", "\na\U{0002}\U{0004}aa\U{0006}a\U{000C}aaa\0\U{0008}\U{000C}aaa\0\U{0008}aaaaa\U{0008}a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{000C}aaa\0\U{0008}aaaaa\U{0008}a", "\na\U{0002}\U{0004}aa\U{0006}a\U{000C}aaa\0\U{0008}\U{000C}aaa\0\U{0008}aaaaa\U{0008}a");
}
method {:test} Test66() {
var r0 := isSubstring("\U{0018}\0aaa\U{0006}\U{000C}\U{0008}aaa\U{0016}\U{000E}", "\U{001A}aaaaaaaa\U{0010}a\U{0012}a\U{0014}a\naaaaaa\U{0004}aaaa\U{0002}a");
expect r0 <==> isSubstringPred("\U{0018}\0aaa\U{0006}\U{000C}\U{0008}aaa\U{0016}\U{000E}", "\U{001A}aaaaaaaa\U{0010}a\U{0012}a\U{0014}a\naaaaaa\U{0004}aaaa\U{0002}a");
expect r0 ==> isSubstringPred("\U{0018}\0aaa\U{0006}\U{000C}\U{0008}aaa\U{0016}\U{000E}", "\U{001A}aaaaaaaa\U{0010}a\U{0012}a\U{0014}a\naaaaaa\U{0004}aaaa\U{0002}a");
expect isSubstringPred("\U{0018}\0aaa\U{0006}\U{000C}\U{0008}aaa\U{0016}\U{000E}", "\U{001A}aaaaaaaa\U{0010}a\U{0012}a\U{0014}a\naaaaaa\U{0004}aaaa\U{0002}a") ==> r0;
expect isSubstringPred("\U{0018}\0aaa\U{0006}\U{000C}\U{0008}aaa\U{0016}\U{000E}", "\U{001A}aaaaaaaa\U{0010}a\U{0012}a\U{0014}a\naaaaaa\U{0004}aaaa\U{0002}a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0018}\0aaa\U{0006}\U{000C}\U{0008}aaa\U{0016}\U{000E}", "\U{001A}aaaaaaaa\U{0010}a\U{0012}a\U{0014}a\naaaaaa\U{0004}aaaa\U{0002}a");
}
method {:test} Test67() {
var r0 := haveCommonKSubstring(30, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(30, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(30, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test68() {
var r0 := haveCommonKSubstring(47, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0008}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa\0a");
expect r0 <==> haveCommonKSubstringPred(47, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0008}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa\0a");
expect !r0 <==> haveNotCommonKSubstringPred(47, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0008}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa\0a");
}
method {:test} Test69() {
expect |"\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| <= |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaa\0aaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 10 - TIME: 90.6884816 s

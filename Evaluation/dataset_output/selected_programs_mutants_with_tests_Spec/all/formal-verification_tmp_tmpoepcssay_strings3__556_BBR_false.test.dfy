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
  return false;
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

// REPEAT 1 - TIME: 12.0150071 s

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
var r0 := isSubstring("\U{0002}", "\U{0004}a\0aaaaaa\U{0002}aaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 <==> isSubstringPred("\U{0002}", "\U{0004}a\0aaaaaa\U{0002}aaaaaaaaaaaaaaaaaa\U{0002}");
expect r0 ==> isSubstringPred("\U{0002}", "\U{0004}a\0aaaaaa\U{0002}aaaaaaaaaaaaaaaaaa\U{0002}");
expect isSubstringPred("\U{0002}", "\U{0004}a\0aaaaaa\U{0002}aaaaaaaaaaaaaaaaaa\U{0002}") ==> r0;
expect isSubstringPred("\U{0002}", "\U{0004}a\0aaaaaa\U{0002}aaaaaaaaaaaaaaaaaa\U{0002}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0002}", "\U{0004}a\0aaaaaa\U{0002}aaaaaaaaaaaaaaaaaa\U{0002}");
}
method {:test} Test10() {
var r0 := isSubstring("aaaaaaaaaaa\U{0002}", "aaaaa\0");
expect r0 <==> isSubstringPred("aaaaaaaaaaa\U{0002}", "aaaaa\0");
expect r0 ==> isSubstringPred("aaaaaaaaaaa\U{0002}", "aaaaa\0");
expect isSubstringPred("aaaaaaaaaaa\U{0002}", "aaaaa\0") ==> r0;
expect isSubstringPred("aaaaaaaaaaa\U{0002}", "aaaaa\0") ==> r0;
expect !r0 <==> isNotSubstringPred("aaaaaaaaaaa\U{0002}", "aaaaa\0");
}
method {:test} Test11() {
var r0 := haveCommonKSubstring(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaa\0aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaa\0aaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaa\0aaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test12() {
var r0 := haveCommonKSubstring(39, "\0", "\U{0002}");
expect r0 <==> haveCommonKSubstringPred(39, "\0", "\U{0002}");
expect !r0 <==> haveNotCommonKSubstringPred(39, "\0", "\U{0002}");
}
method {:test} Test13() {
expect |"\0aaaaaaaaaaaaaaaaaaaa"| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0aaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\0aaaaaaaaaaaaaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "\0aaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\0aaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 2 - TIME: 19.7169804 s

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
var r0 := isSubstring("\U{0004}\0aaaaaaaa", "\U{0002}aaaaaaaaaaaaaa\U{0004}\0aaa\U{0004}\0aaaaaaaa");
expect r0 <==> isSubstringPred("\U{0004}\0aaaaaaaa", "\U{0002}aaaaaaaaaaaaaa\U{0004}\0aaa\U{0004}\0aaaaaaaa");
expect r0 ==> isSubstringPred("\U{0004}\0aaaaaaaa", "\U{0002}aaaaaaaaaaaaaa\U{0004}\0aaa\U{0004}\0aaaaaaaa");
expect isSubstringPred("\U{0004}\0aaaaaaaa", "\U{0002}aaaaaaaaaaaaaa\U{0004}\0aaa\U{0004}\0aaaaaaaa") ==> r0;
expect isSubstringPred("\U{0004}\0aaaaaaaa", "\U{0002}aaaaaaaaaaaaaa\U{0004}\0aaa\U{0004}\0aaaaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}\0aaaaaaaa", "\U{0002}aaaaaaaaaaaaaa\U{0004}\0aaa\U{0004}\0aaaaaaaa");
}
method {:test} Test17() {
var r0 := isSubstring("a\0", "\U{0004}aaaaa\U{0002}");
expect r0 <==> isSubstringPred("a\0", "\U{0004}aaaaa\U{0002}");
expect r0 ==> isSubstringPred("a\0", "\U{0004}aaaaa\U{0002}");
expect isSubstringPred("a\0", "\U{0004}aaaaa\U{0002}") ==> r0;
expect isSubstringPred("a\0", "\U{0004}aaaaa\U{0002}") ==> r0;
expect !r0 <==> isNotSubstringPred("a\0", "\U{0004}aaaaa\U{0002}");
}
method {:test} Test18() {
var r0 := haveCommonKSubstring(24, "aa\0aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(24, "aa\0aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(24, "aa\0aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test19() {
var r0 := haveCommonKSubstring(40, "\U{0006}aaaaaaaaaaaaa\0aaaaaaa\U{0002}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <==> haveCommonKSubstringPred(40, "\U{0006}aaaaaaaaaaaaa\0aaaaaaa\U{0002}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect !r0 <==> haveNotCommonKSubstringPred(40, "\U{0006}aaaaaaaaaaaaa\0aaaaaaa\U{0002}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa\U{0004}");
}
method {:test} Test20() {
expect |"\0aaaaaaaaaaaaaaaaaaaa\U{0004}a"| <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0aaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\0aaaaaaaaaaaaaaaaaaaa\U{0004}a"| ==> !haveCommonKSubstringPred(k, "\0aaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\0aaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0002}aaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 3 - TIME: 27.0011412 s

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
var r0 := isSubstring("\U{0004}\0a", "\U{0002}\U{0004}\0\U{0004}\0a");
expect r0 <==> isSubstringPred("\U{0004}\0a", "\U{0002}\U{0004}\0\U{0004}\0a");
expect r0 ==> isSubstringPred("\U{0004}\0a", "\U{0002}\U{0004}\0\U{0004}\0a");
expect isSubstringPred("\U{0004}\0a", "\U{0002}\U{0004}\0\U{0004}\0a") ==> r0;
expect isSubstringPred("\U{0004}\0a", "\U{0002}\U{0004}\0\U{0004}\0a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}\0a", "\U{0002}\U{0004}\0\U{0004}\0a");
}
method {:test} Test24() {
var r0 := isSubstring("\U{0002}\0", "\U{0004}");
expect r0 <==> isSubstringPred("\U{0002}\0", "\U{0004}");
expect r0 ==> isSubstringPred("\U{0002}\0", "\U{0004}");
expect isSubstringPred("\U{0002}\0", "\U{0004}") ==> r0;
expect isSubstringPred("\U{0002}\0", "\U{0004}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0002}\0", "\U{0004}");
}
method {:test} Test25() {
var r0 := haveCommonKSubstring(25, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect r0 <==> haveCommonKSubstringPred(25, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}");
expect !r0 <==> haveNotCommonKSubstringPred(25, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}");
}
method {:test} Test26() {
var r0 := haveCommonKSubstring(41, "\U{0002}a", "\U{0004}\0");
expect r0 <==> haveCommonKSubstringPred(41, "\U{0002}a", "\U{0004}\0");
expect !r0 <==> haveNotCommonKSubstringPred(41, "\U{0002}a", "\U{0004}\0");
}
method {:test} Test27() {
expect |"\U{0004}aaaaa\0"| <= |"\U{0002}aaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaa\0", "\U{0002}aaaaaaaa");
expect forall k :: r0 < k <= |"\U{0004}aaaaa\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaa\0", "\U{0002}aaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaa\0", "\U{0002}aaaaaaaa");
}

// REPEAT 4 - TIME: 34.1202995 s

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
var r0 := isSubstring("\U{0006}a\0aaaaaaaa\U{0002}\n", "\U{000C}aaaa\U{0004}\U{0008}a\U{0006}a\0\U{0006}a\0aaaaa\U{0002}\na\U{0002}\naaaaaa");
expect r0 <==> isSubstringPred("\U{0006}a\0aaaaaaaa\U{0002}\n", "\U{000C}aaaa\U{0004}\U{0008}a\U{0006}a\0\U{0006}a\0aaaaa\U{0002}\na\U{0002}\naaaaaa");
expect r0 ==> isSubstringPred("\U{0006}a\0aaaaaaaa\U{0002}\n", "\U{000C}aaaa\U{0004}\U{0008}a\U{0006}a\0\U{0006}a\0aaaaa\U{0002}\na\U{0002}\naaaaaa");
expect isSubstringPred("\U{0006}a\0aaaaaaaa\U{0002}\n", "\U{000C}aaaa\U{0004}\U{0008}a\U{0006}a\0\U{0006}a\0aaaaa\U{0002}\na\U{0002}\naaaaaa") ==> r0;
expect isSubstringPred("\U{0006}a\0aaaaaaaa\U{0002}\n", "\U{000C}aaaa\U{0004}\U{0008}a\U{0006}a\0\U{0006}a\0aaaaa\U{0002}\na\U{0002}\naaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0006}a\0aaaaaaaa\U{0002}\n", "\U{000C}aaaa\U{0004}\U{0008}a\U{0006}a\0\U{0006}a\0aaaaa\U{0002}\na\U{0002}\naaaaaa");
}
method {:test} Test31() {
var r0 := isSubstring("\U{0008}\U{0004}\U{0002}", "\U{0006}\0");
expect r0 <==> isSubstringPred("\U{0008}\U{0004}\U{0002}", "\U{0006}\0");
expect r0 ==> isSubstringPred("\U{0008}\U{0004}\U{0002}", "\U{0006}\0");
expect isSubstringPred("\U{0008}\U{0004}\U{0002}", "\U{0006}\0") ==> r0;
expect isSubstringPred("\U{0008}\U{0004}\U{0002}", "\U{0006}\0") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0008}\U{0004}\U{0002}", "\U{0006}\0");
}
method {:test} Test32() {
var r0 := haveCommonKSubstring(26, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a", "\U{0008}aa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> haveCommonKSubstringPred(26, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a", "\U{0008}aa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect !r0 <==> haveNotCommonKSubstringPred(26, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaa\U{0002}a", "\U{0008}aa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
}
method {:test} Test33() {
var r0 := haveCommonKSubstring(42, "\U{0014}aa\U{0006}aaaaaaaaaaaaaaa\U{0002}aa\U{0008}\naaaaa\U{0012}", "\U{0016}\U{0004}aaaaaaaaaaaaaaaaaaaaa\0\U{000C}\U{000E}aa\U{0010}");
expect r0 <==> haveCommonKSubstringPred(42, "\U{0014}aa\U{0006}aaaaaaaaaaaaaaa\U{0002}aa\U{0008}\naaaaa\U{0012}", "\U{0016}\U{0004}aaaaaaaaaaaaaaaaaaaaa\0\U{000C}\U{000E}aa\U{0010}");
expect !r0 <==> haveNotCommonKSubstringPred(42, "\U{0014}aa\U{0006}aaaaaaaaaaaaaaa\U{0002}aa\U{0008}\naaaaa\U{0012}", "\U{0016}\U{0004}aaaaaaaaaaaaaaaaaaaaa\0\U{000C}\U{000E}aa\U{0010}");
}
method {:test} Test34() {
expect |"\0a"| <= |"\U{0002}a"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0a", "\U{0002}a");
expect forall k :: r0 < k <= |"\0a"| ==> !haveCommonKSubstringPred(k, "\0a", "\U{0002}a");
expect haveCommonKSubstringPred(r0, "\0a", "\U{0002}a");
}

// REPEAT 5 - TIME: 41.6664074 s

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
var r0 := isSubstring("\U{0002}aa", "\0\U{0002}\U{0002}aa");
expect r0 <==> isSubstringPred("\U{0002}aa", "\0\U{0002}\U{0002}aa");
expect r0 ==> isSubstringPred("\U{0002}aa", "\0\U{0002}\U{0002}aa");
expect isSubstringPred("\U{0002}aa", "\0\U{0002}\U{0002}aa") ==> r0;
expect isSubstringPred("\U{0002}aa", "\0\U{0002}\U{0002}aa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0002}aa", "\0\U{0002}\U{0002}aa");
}
method {:test} Test38() {
var r0 := isSubstring("\U{0006}\0a\U{0002}", "\U{0008}aaaaaa\U{0004}");
expect r0 <==> isSubstringPred("\U{0006}\0a\U{0002}", "\U{0008}aaaaaa\U{0004}");
expect r0 ==> isSubstringPred("\U{0006}\0a\U{0002}", "\U{0008}aaaaaa\U{0004}");
expect isSubstringPred("\U{0006}\0a\U{0002}", "\U{0008}aaaaaa\U{0004}") ==> r0;
expect isSubstringPred("\U{0006}\0a\U{0002}", "\U{0008}aaaaaa\U{0004}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0006}\0a\U{0002}", "\U{0008}aaaaaa\U{0004}");
}
method {:test} Test39() {
var r0 := haveCommonKSubstring(27, "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(27, "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(27, "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test40() {
var r0 := haveCommonKSubstring(43, "\U{0006}\U{0002}aaaaaaaaaaa\0aaaaaaaaaa", "\U{0004}aa");
expect r0 <==> haveCommonKSubstringPred(43, "\U{0006}\U{0002}aaaaaaaaaaa\0aaaaaaaaaa", "\U{0004}aa");
expect !r0 <==> haveNotCommonKSubstringPred(43, "\U{0006}\U{0002}aaaaaaaaaaa\0aaaaaaaaaa", "\U{0004}aa");
}
method {:test} Test41() {
expect |"\U{0004}aa\0aaaaaaaaa"| <= |"\U{0002}aaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aa\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0004}aa\0aaaaaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0004}aa\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aa\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaaaa");
}

// REPEAT 6 - TIME: 48.04365 s

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
var r0 := isSubstring("\0a\U{0004}\0a", "\U{0006}\U{0002}\0a\U{0004}\0a\U{0004}\0a");
expect r0 <==> isSubstringPred("\0a\U{0004}\0a", "\U{0006}\U{0002}\0a\U{0004}\0a\U{0004}\0a");
expect r0 ==> isSubstringPred("\0a\U{0004}\0a", "\U{0006}\U{0002}\0a\U{0004}\0a\U{0004}\0a");
expect isSubstringPred("\0a\U{0004}\0a", "\U{0006}\U{0002}\0a\U{0004}\0a\U{0004}\0a") ==> r0;
expect isSubstringPred("\0a\U{0004}\0a", "\U{0006}\U{0002}\0a\U{0004}\0a\U{0004}\0a") ==> r0;
expect !r0 <==> isNotSubstringPred("\0a\U{0004}\0a", "\U{0006}\U{0002}\0a\U{0004}\0a\U{0004}\0a");
}
method {:test} Test45() {
var r0 := isSubstring("\U{0010}\U{0002}aaaaaaa\U{0008}a\U{0004}", "\U{0012}\U{0006}aaa\na\U{000C}aaaaa\U{000E}aaaaaaaaaaaaaaa\0");
expect r0 <==> isSubstringPred("\U{0010}\U{0002}aaaaaaa\U{0008}a\U{0004}", "\U{0012}\U{0006}aaa\na\U{000C}aaaaa\U{000E}aaaaaaaaaaaaaaa\0");
expect r0 ==> isSubstringPred("\U{0010}\U{0002}aaaaaaa\U{0008}a\U{0004}", "\U{0012}\U{0006}aaa\na\U{000C}aaaaa\U{000E}aaaaaaaaaaaaaaa\0");
expect isSubstringPred("\U{0010}\U{0002}aaaaaaa\U{0008}a\U{0004}", "\U{0012}\U{0006}aaa\na\U{000C}aaaaa\U{000E}aaaaaaaaaaaaaaa\0") ==> r0;
expect isSubstringPred("\U{0010}\U{0002}aaaaaaa\U{0008}a\U{0004}", "\U{0012}\U{0006}aaa\na\U{000C}aaaaa\U{000E}aaaaaaaaaaaaaaa\0") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0010}\U{0002}aaaaaaa\U{0008}a\U{0004}", "\U{0012}\U{0006}aaa\na\U{000C}aaaaa\U{000E}aaaaaaaaaaaaaaa\0");
}
method {:test} Test46() {
var r0 := haveCommonKSubstring(28, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(28, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(28, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test47() {
var r0 := haveCommonKSubstring(44, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "\U{0008}\0a\U{0004}");
expect r0 <==> haveCommonKSubstringPred(44, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "\U{0008}\0a\U{0004}");
expect !r0 <==> haveNotCommonKSubstringPred(44, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "\U{0008}\0a\U{0004}");
}
method {:test} Test48() {
expect |"\U{0006}aaaaa\0aaaaaaa"| <= |"\U{0004}aaaaaaaaaaa\U{0002}aaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}aaaaa\0aaaaaaa", "\U{0004}aaaaaaaaaaa\U{0002}aaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0006}aaaaa\0aaaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0006}aaaaa\0aaaaaaa", "\U{0004}aaaaaaaaaaa\U{0002}aaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0006}aaaaa\0aaaaaaa", "\U{0004}aaaaaaaaaaa\U{0002}aaaaaaaaa");
}

// REPEAT 7 - TIME: 53.3325076 s

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
var r0 := isSubstring("a\0\U{0004}\U{0006}aaaaa\U{0014}\U{0010}\U{0012}\na", "\U{0016}aaaa\U{0008}\U{000C}a\U{0002}a\U{000E}a\0\U{0004}\U{0006}a\0\U{0004}\U{0006}a\U{0014}\U{0010}\U{0012}\n\U{0014}\U{0010}\U{0012}\na");
expect r0 <==> isSubstringPred("a\0\U{0004}\U{0006}aaaaa\U{0014}\U{0010}\U{0012}\na", "\U{0016}aaaa\U{0008}\U{000C}a\U{0002}a\U{000E}a\0\U{0004}\U{0006}a\0\U{0004}\U{0006}a\U{0014}\U{0010}\U{0012}\n\U{0014}\U{0010}\U{0012}\na");
expect r0 ==> isSubstringPred("a\0\U{0004}\U{0006}aaaaa\U{0014}\U{0010}\U{0012}\na", "\U{0016}aaaa\U{0008}\U{000C}a\U{0002}a\U{000E}a\0\U{0004}\U{0006}a\0\U{0004}\U{0006}a\U{0014}\U{0010}\U{0012}\n\U{0014}\U{0010}\U{0012}\na");
expect isSubstringPred("a\0\U{0004}\U{0006}aaaaa\U{0014}\U{0010}\U{0012}\na", "\U{0016}aaaa\U{0008}\U{000C}a\U{0002}a\U{000E}a\0\U{0004}\U{0006}a\0\U{0004}\U{0006}a\U{0014}\U{0010}\U{0012}\n\U{0014}\U{0010}\U{0012}\na") ==> r0;
expect isSubstringPred("a\0\U{0004}\U{0006}aaaaa\U{0014}\U{0010}\U{0012}\na", "\U{0016}aaaa\U{0008}\U{000C}a\U{0002}a\U{000E}a\0\U{0004}\U{0006}a\0\U{0004}\U{0006}a\U{0014}\U{0010}\U{0012}\n\U{0014}\U{0010}\U{0012}\na") ==> r0;
expect !r0 <==> isNotSubstringPred("a\0\U{0004}\U{0006}aaaaa\U{0014}\U{0010}\U{0012}\na", "\U{0016}aaaa\U{0008}\U{000C}a\U{0002}a\U{000E}a\0\U{0004}\U{0006}a\0\U{0004}\U{0006}a\U{0014}\U{0010}\U{0012}\n\U{0014}\U{0010}\U{0012}\na");
}
method {:test} Test52() {
var r0 := isSubstring("\U{000C}aa\na\U{000E}\U{0004}aaa\U{0014}\U{0006}\U{0008}\U{0018}", "\U{001C}\U{0002}aaaaa\U{0010}aaaa\0\U{0012}aaaaaaaaa\U{0016}aaaaa\U{001A}");
expect r0 <==> isSubstringPred("\U{000C}aa\na\U{000E}\U{0004}aaa\U{0014}\U{0006}\U{0008}\U{0018}", "\U{001C}\U{0002}aaaaa\U{0010}aaaa\0\U{0012}aaaaaaaaa\U{0016}aaaaa\U{001A}");
expect r0 ==> isSubstringPred("\U{000C}aa\na\U{000E}\U{0004}aaa\U{0014}\U{0006}\U{0008}\U{0018}", "\U{001C}\U{0002}aaaaa\U{0010}aaaa\0\U{0012}aaaaaaaaa\U{0016}aaaaa\U{001A}");
expect isSubstringPred("\U{000C}aa\na\U{000E}\U{0004}aaa\U{0014}\U{0006}\U{0008}\U{0018}", "\U{001C}\U{0002}aaaaa\U{0010}aaaa\0\U{0012}aaaaaaaaa\U{0016}aaaaa\U{001A}") ==> r0;
expect isSubstringPred("\U{000C}aa\na\U{000E}\U{0004}aaa\U{0014}\U{0006}\U{0008}\U{0018}", "\U{001C}\U{0002}aaaaa\U{0010}aaaa\0\U{0012}aaaaaaaaa\U{0016}aaaaa\U{001A}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{000C}aa\na\U{000E}\U{0004}aaa\U{0014}\U{0006}\U{0008}\U{0018}", "\U{001C}\U{0002}aaaaa\U{0010}aaaa\0\U{0012}aaaaaaaaa\U{0016}aaaaa\U{001A}");
}
method {:test} Test53() {
var r0 := haveCommonKSubstring(29, "\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(29, "\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(29, "\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0\U{0004}a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test54() {
var r0 := haveCommonKSubstring(45, "\U{0014}aaaaaaaaa\0aaaaaaaaaaaa\U{0004}aaa\U{0008}a\U{000E}", "\U{0012}aaaaaaaaaa\U{0002}aa\U{0006}aaaaaaaaa\naaa\U{000C}\U{0010}");
expect r0 <==> haveCommonKSubstringPred(45, "\U{0014}aaaaaaaaa\0aaaaaaaaaaaa\U{0004}aaa\U{0008}a\U{000E}", "\U{0012}aaaaaaaaaa\U{0002}aa\U{0006}aaaaaaaaa\naaa\U{000C}\U{0010}");
expect !r0 <==> haveNotCommonKSubstringPred(45, "\U{0014}aaaaaaaaa\0aaaaaaaaaaaa\U{0004}aaa\U{0008}a\U{000E}", "\U{0012}aaaaaaaaaa\U{0002}aa\U{0006}aaaaaaaaa\naaa\U{000C}\U{0010}");
}
method {:test} Test55() {
expect |"\U{0006}aaaaaa\U{0002}aaaaaa"| <= |"\0aaaaaa\U{0004}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0006}aaaaaa\U{0002}aaaaaa", "\0aaaaaa\U{0004}aaaaaa");
expect forall k :: r0 < k <= |"\U{0006}aaaaaa\U{0002}aaaaaa"| ==> !haveCommonKSubstringPred(k, "\U{0006}aaaaaa\U{0002}aaaaaa", "\0aaaaaa\U{0004}aaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0006}aaaaaa\U{0002}aaaaaa", "\0aaaaaa\U{0004}aaaaaa");
}

// REPEAT 8 - TIME: 58.6134115 s

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
var r0 := isSubstring("\U{0006}\0a", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aa");
expect r0 <==> isSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aa");
expect r0 ==> isSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aa");
expect isSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aa") ==> r0;
expect isSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aa");
}
method {:test} Test59() {
var r0 := isSubstring("\U{0004}aaaaaaaaaaaa", "\U{0002}\0a");
expect r0 <==> isSubstringPred("\U{0004}aaaaaaaaaaaa", "\U{0002}\0a");
expect r0 ==> isSubstringPred("\U{0004}aaaaaaaaaaaa", "\U{0002}\0a");
expect isSubstringPred("\U{0004}aaaaaaaaaaaa", "\U{0002}\0a") ==> r0;
expect isSubstringPred("\U{0004}aaaaaaaaaaaa", "\U{0002}\0a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}aaaaaaaaaaaa", "\U{0002}\0a");
}
method {:test} Test60() {
var r0 := haveCommonKSubstring(30, "\U{0004}\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(30, "\U{0004}\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(30, "\U{0004}\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaa", "\U{0004}\U{0002}aaaaaaaaa\0aaaaaaaaaaaaaaaaaa");
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(46, "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}", "\naa\U{0004}\0");
expect r0 <==> haveCommonKSubstringPred(46, "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}", "\naa\U{0004}\0");
expect !r0 <==> haveNotCommonKSubstringPred(46, "\U{000C}\U{0002}aaaaaaaaaaaaaaaaaaaaa\U{0006}a\U{0008}", "\naa\U{0004}\0");
}
method {:test} Test62() {
expect |"\U{0004}aaaaa\0"| <= |"\U{0002}aaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaa\0", "\U{0002}aaaaaa");
expect forall k :: r0 < k <= |"\U{0004}aaaaa\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaa\0", "\U{0002}aaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaa\0", "\U{0002}aaaaaa");
}

// REPEAT 9 - TIME: 64.4256976 s

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
var r0 := isSubstring("\U{0004}\0", "\U{0002}\U{0004}\0\U{0004}\0");
expect r0 <==> isSubstringPred("\U{0004}\0", "\U{0002}\U{0004}\0\U{0004}\0");
expect r0 ==> isSubstringPred("\U{0004}\0", "\U{0002}\U{0004}\0\U{0004}\0");
expect isSubstringPred("\U{0004}\0", "\U{0002}\U{0004}\0\U{0004}\0") ==> r0;
expect isSubstringPred("\U{0004}\0", "\U{0002}\U{0004}\0\U{0004}\0") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}\0", "\U{0002}\U{0004}\0\U{0004}\0");
}
method {:test} Test66() {
var r0 := isSubstring("\U{0016}a\U{0006}\U{0002}a\U{000C}aaaaa\U{0014}a", "\U{0018}\U{0004}a\naaa\U{0010}aa\U{0012}aaaaa\U{000E}aaaa\U{0008}aaaaa\0");
expect r0 <==> isSubstringPred("\U{0016}a\U{0006}\U{0002}a\U{000C}aaaaa\U{0014}a", "\U{0018}\U{0004}a\naaa\U{0010}aa\U{0012}aaaaa\U{000E}aaaa\U{0008}aaaaa\0");
expect r0 ==> isSubstringPred("\U{0016}a\U{0006}\U{0002}a\U{000C}aaaaa\U{0014}a", "\U{0018}\U{0004}a\naaa\U{0010}aa\U{0012}aaaaa\U{000E}aaaa\U{0008}aaaaa\0");
expect isSubstringPred("\U{0016}a\U{0006}\U{0002}a\U{000C}aaaaa\U{0014}a", "\U{0018}\U{0004}a\naaa\U{0010}aa\U{0012}aaaaa\U{000E}aaaa\U{0008}aaaaa\0") ==> r0;
expect isSubstringPred("\U{0016}a\U{0006}\U{0002}a\U{000C}aaaaa\U{0014}a", "\U{0018}\U{0004}a\naaa\U{0010}aa\U{0012}aaaaa\U{000E}aaaa\U{0008}aaaaa\0") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0016}a\U{0006}\U{0002}a\U{000C}aaaaa\U{0014}a", "\U{0018}\U{0004}a\naaa\U{0010}aa\U{0012}aaaaa\U{000E}aaaa\U{0008}aaaaa\0");
}
method {:test} Test67() {
var r0 := haveCommonKSubstring(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test68() {
var r0 := haveCommonKSubstring(47, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0a");
expect r0 <==> haveCommonKSubstringPred(47, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0a");
expect !r0 <==> haveNotCommonKSubstringPred(47, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0a");
}
method {:test} Test69() {
expect |"\0a"| <= |"\U{0002}aaaaaa\U{0004}aaaaaa\U{0006}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\0a", "\U{0002}aaaaaa\U{0004}aaaaaa\U{0006}aaa");
expect forall k :: r0 < k <= |"\0a"| ==> !haveCommonKSubstringPred(k, "\0a", "\U{0002}aaaaaa\U{0004}aaaaaa\U{0006}aaa");
expect haveCommonKSubstringPred(r0, "\0a", "\U{0002}aaaaaa\U{0004}aaaaaa\U{0006}aaa");
}

// REPEAT 10 - TIME: 70.0497537 s

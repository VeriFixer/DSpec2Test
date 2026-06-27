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
var r0 := isSubstring("aaaaaaaaaaa", "aaaaaaaaaaaa");
expect r0 <==> isSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa");
expect r0 ==> isSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa");
expect isSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa") ==> r0;
expect isSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("aaaaaaaaaaa", "aaaaaaaaaaaa");
}
method {:test} Test22() {
var r0 := isSubstring("", "aaaaaaaaaaa");
expect r0 <==> isSubstringPred("", "aaaaaaaaaaa");
expect r0 ==> isSubstringPred("", "aaaaaaaaaaa");
expect isSubstringPred("", "aaaaaaaaaaa") ==> r0;
expect isSubstringPred("", "aaaaaaaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("", "aaaaaaaaaaa");
}
method {:test} Test23() {
var r0 := isSubstring("a", "aaaaaaaaaaa");
expect r0 <==> isSubstringPred("a", "aaaaaaaaaaa");
expect r0 ==> isSubstringPred("a", "aaaaaaaaaaa");
expect isSubstringPred("a", "aaaaaaaaaaa") ==> r0;
expect isSubstringPred("a", "aaaaaaaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("a", "aaaaaaaaaaa");
}
method {:test} Test24() {
var r0 := isSubstring("aaaa", "aaaaaaaaaaaaaaaaaaaa");
expect r0 <==> isSubstringPred("aaaa", "aaaaaaaaaaaaaaaaaaaa");
expect r0 ==> isSubstringPred("aaaa", "aaaaaaaaaaaaaaaaaaaa");
expect isSubstringPred("aaaa", "aaaaaaaaaaaaaaaaaaaa") ==> r0;
expect isSubstringPred("aaaa", "aaaaaaaaaaaaaaaaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("aaaa", "aaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test25() {
var r0 := isSubstring("", "");
expect r0 <==> isSubstringPred("", "");
expect r0 ==> isSubstringPred("", "");
expect isSubstringPred("", "") ==> r0;
expect isSubstringPred("", "") ==> r0;
expect !r0 <==> isNotSubstringPred("", "");
}
method {:test} Test26() {
var r0 := isSubstring("", "a");
expect r0 <==> isSubstringPred("", "a");
expect r0 ==> isSubstringPred("", "a");
expect isSubstringPred("", "a") ==> r0;
expect isSubstringPred("", "a") ==> r0;
expect !r0 <==> isNotSubstringPred("", "a");
}
method {:test} Test27() {
var r0 := isSubstring("a", "aa");
expect r0 <==> isSubstringPred("a", "aa");
expect r0 ==> isSubstringPred("a", "aa");
expect isSubstringPred("a", "aa") ==> r0;
expect isSubstringPred("a", "aa") ==> r0;
expect !r0 <==> isNotSubstringPred("a", "aa");
}
method {:test} Test34() {
var r0 := isSubstring("a", "");
expect r0 <==> isSubstringPred("a", "");
expect r0 ==> isSubstringPred("a", "");
expect isSubstringPred("a", "") ==> r0;
expect isSubstringPred("a", "") ==> r0;
expect !r0 <==> isNotSubstringPred("a", "");
}
method {:test} Test35() {
var r0 := isSubstring("aa", "");
expect r0 <==> isSubstringPred("aa", "");
expect r0 ==> isSubstringPred("aa", "");
expect isSubstringPred("aa", "") ==> r0;
expect isSubstringPred("aa", "") ==> r0;
expect !r0 <==> isNotSubstringPred("aa", "");
}
method {:test} Test38() {
var r0 := isSubstring("", "aa");
expect r0 <==> isSubstringPred("", "aa");
expect r0 ==> isSubstringPred("", "aa");
expect isSubstringPred("", "aa") ==> r0;
expect isSubstringPred("", "aa") ==> r0;
expect !r0 <==> isNotSubstringPred("", "aa");
}
method {:test} Test43() {
var r0 := haveCommonKSubstring(21, "aaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(21, "aaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(21, "aaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test44() {
var r0 := haveCommonKSubstring(0, "", "aaaaaaa");
expect r0 <==> haveCommonKSubstringPred(0, "", "aaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(0, "", "aaaaaaa");
}
method {:test} Test45() {
var r0 := haveCommonKSubstring(0, "a", "aaa");
expect r0 <==> haveCommonKSubstringPred(0, "a", "aaa");
expect !r0 <==> haveNotCommonKSubstringPred(0, "a", "aaa");
}
method {:test} Test46() {
var r0 := haveCommonKSubstring(1, "aa", "aaaaaaa");
expect r0 <==> haveCommonKSubstringPred(1, "aa", "aaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(1, "aa", "aaaaaaa");
}
method {:test} Test47() {
var r0 := haveCommonKSubstring(0, "aaaaaa", "");
expect r0 <==> haveCommonKSubstringPred(0, "aaaaaa", "");
expect !r0 <==> haveNotCommonKSubstringPred(0, "aaaaaa", "");
}
method {:test} Test48() {
var r0 := haveCommonKSubstring(0, "aaaaaaaaaaaaaaaaaaaaaaaa", "a");
expect r0 <==> haveCommonKSubstringPred(0, "aaaaaaaaaaaaaaaaaaaaaaaa", "a");
expect !r0 <==> haveNotCommonKSubstringPred(0, "aaaaaaaaaaaaaaaaaaaaaaaa", "a");
}
method {:test} Test49() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aa");
expect r0 <==> haveCommonKSubstringPred(1, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aa");
expect !r0 <==> haveNotCommonKSubstringPred(1, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aa");
}
method {:test} Test50() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(1, "aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(1, "aaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test52() {
var r0 := haveCommonKSubstring(23, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(23, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(23, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test54() {
var r0 := haveCommonKSubstring(38, "", "");
expect r0 <==> haveCommonKSubstringPred(38, "", "");
expect !r0 <==> haveNotCommonKSubstringPred(38, "", "");
}
method {:test} Test55() {
var r0 := haveCommonKSubstring(100, "", "");
expect r0 <==> haveCommonKSubstringPred(100, "", "");
expect !r0 <==> haveNotCommonKSubstringPred(100, "", "");
}
method {:test} Test57() {
var r0 := haveCommonKSubstring(38, "a", "");
expect r0 <==> haveCommonKSubstringPred(38, "a", "");
expect !r0 <==> haveNotCommonKSubstringPred(38, "a", "");
}
method {:test} Test58() {
var r0 := haveCommonKSubstring(38, "aa", "");
expect r0 <==> haveCommonKSubstringPred(38, "aa", "");
expect !r0 <==> haveNotCommonKSubstringPred(38, "aa", "");
}
method {:test} Test60() {
var r0 := haveCommonKSubstring(38, "", "a");
expect r0 <==> haveCommonKSubstringPred(38, "", "a");
expect !r0 <==> haveNotCommonKSubstringPred(38, "", "a");
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(38, "", "aa");
expect r0 <==> haveCommonKSubstringPred(38, "", "aa");
expect !r0 <==> haveNotCommonKSubstringPred(38, "", "aa");
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

// REPEAT 1 - TIME: 85.4563745 s

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
var r0 := isSubstring("\U{0002}\U{0004}aaa", "\U{0006}a\0\U{0002}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa");
expect r0 <==> isSubstringPred("\U{0002}\U{0004}aaa", "\U{0006}a\0\U{0002}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa");
expect r0 ==> isSubstringPred("\U{0002}\U{0004}aaa", "\U{0006}a\0\U{0002}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa");
expect isSubstringPred("\U{0002}\U{0004}aaa", "\U{0006}a\0\U{0002}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa") ==> r0;
expect isSubstringPred("\U{0002}\U{0004}aaa", "\U{0006}a\0\U{0002}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0002}\U{0004}aaa", "\U{0006}a\0\U{0002}\U{0004}aaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaa");
}
method {:test} Test79() {
var r0 := isSubstring("\n\U{0004}\0", "\U{000C}aaaa\U{0002}\U{0006}\U{0008}");
expect r0 <==> isSubstringPred("\n\U{0004}\0", "\U{000C}aaaa\U{0002}\U{0006}\U{0008}");
expect r0 ==> isSubstringPred("\n\U{0004}\0", "\U{000C}aaaa\U{0002}\U{0006}\U{0008}");
expect isSubstringPred("\n\U{0004}\0", "\U{000C}aaaa\U{0002}\U{0006}\U{0008}") ==> r0;
expect isSubstringPred("\n\U{0004}\0", "\U{000C}aaaa\U{0002}\U{0006}\U{0008}") ==> r0;
expect !r0 <==> isNotSubstringPred("\n\U{0004}\0", "\U{000C}aaaa\U{0002}\U{0006}\U{0008}");
}
method {:test} Test80() {
var r0 := haveCommonKSubstring(24, "\U{0006}aa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(24, "\U{0006}aa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(24, "\U{0006}aa\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\0a\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test81() {
var r0 := haveCommonKSubstring(101, "\U{000C}\U{0004}\U{0008}aaa\0", "\U{000E}aaaaaaaaaaaaaa\U{0006}\U{0002}aaa\n");
expect r0 <==> haveCommonKSubstringPred(101, "\U{000C}\U{0004}\U{0008}aaa\0", "\U{000E}aaaaaaaaaaaaaa\U{0006}\U{0002}aaa\n");
expect !r0 <==> haveNotCommonKSubstringPred(101, "\U{000C}\U{0004}\U{0008}aaa\0", "\U{000E}aaaaaaaaaaaaaa\U{0006}\U{0002}aaa\n");
}
method {:test} Test82() {
expect |"\U{0004}aaaaa\U{0006}"| <= |"\U{0002}aaaa\0aa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aaaaa\U{0006}", "\U{0002}aaaa\0aa");
expect forall k :: r0 < k <= |"\U{0004}aaaaa\U{0006}"| ==> !haveCommonKSubstringPred(k, "\U{0004}aaaaa\U{0006}", "\U{0002}aaaa\0aa");
expect haveCommonKSubstringPred(r0, "\U{0004}aaaaa\U{0006}", "\U{0002}aaaa\0aa");
}

// REPEAT 2 - TIME: 90.4646121 s

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
var r0 := isSubstring("aaa\U{0002}\U{0004}a", "\0aaaaa\U{0002}\U{0004}aaaaaa\U{0002}\U{0004}a");
expect r0 <==> isSubstringPred("aaa\U{0002}\U{0004}a", "\0aaaaa\U{0002}\U{0004}aaaaaa\U{0002}\U{0004}a");
expect r0 ==> isSubstringPred("aaa\U{0002}\U{0004}a", "\0aaaaa\U{0002}\U{0004}aaaaaa\U{0002}\U{0004}a");
expect isSubstringPred("aaa\U{0002}\U{0004}a", "\0aaaaa\U{0002}\U{0004}aaaaaa\U{0002}\U{0004}a") ==> r0;
expect isSubstringPred("aaa\U{0002}\U{0004}a", "\0aaaaa\U{0002}\U{0004}aaaaaa\U{0002}\U{0004}a") ==> r0;
expect !r0 <==> isNotSubstringPred("aaa\U{0002}\U{0004}a", "\0aaaaa\U{0002}\U{0004}aaaaaa\U{0002}\U{0004}a");
}
method {:test} Test86() {
var r0 := isSubstring("\U{0004}\U{0002}aaa\U{0006}aaaaa\U{0008}", "\n\0a");
expect r0 <==> isSubstringPred("\U{0004}\U{0002}aaa\U{0006}aaaaa\U{0008}", "\n\0a");
expect r0 ==> isSubstringPred("\U{0004}\U{0002}aaa\U{0006}aaaaa\U{0008}", "\n\0a");
expect isSubstringPred("\U{0004}\U{0002}aaa\U{0006}aaaaa\U{0008}", "\n\0a") ==> r0;
expect isSubstringPred("\U{0004}\U{0002}aaa\U{0006}aaaaa\U{0008}", "\n\0a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}\U{0002}aaa\U{0006}aaaaa\U{0008}", "\n\0a");
}
method {:test} Test87() {
var r0 := haveCommonKSubstring(25, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0008}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect r0 <==> haveCommonKSubstringPred(25, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0008}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect !r0 <==> haveNotCommonKSubstringPred(25, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0008}a\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaa\0");
}
method {:test} Test88() {
var r0 := haveCommonKSubstring(102, "\naaaa\U{0002}\U{0006}a", "\U{0008}\0aaaaaaaaaaaaaaaaa\U{0004}aa");
expect r0 <==> haveCommonKSubstringPred(102, "\naaaa\U{0002}\U{0006}a", "\U{0008}\0aaaaaaaaaaaaaaaaa\U{0004}aa");
expect !r0 <==> haveNotCommonKSubstringPred(102, "\naaaa\U{0002}\U{0006}a", "\U{0008}\0aaaaaaaaaaaaaaaaa\U{0004}aa");
}
method {:test} Test89() {
expect |"\U{0008}\0\U{0006}aa"| <= |"\U{0004}\U{0002}aaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}\0\U{0006}aa", "\U{0004}\U{0002}aaaaa");
expect forall k :: r0 < k <= |"\U{0008}\0\U{0006}aa"| ==> !haveCommonKSubstringPred(k, "\U{0008}\0\U{0006}aa", "\U{0004}\U{0002}aaaaa");
expect haveCommonKSubstringPred(r0, "\U{0008}\0\U{0006}aa", "\U{0004}\U{0002}aaaaa");
}

// REPEAT 3 - TIME: 95.1573105 s

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
var r0 := isSubstring("\U{0002}a", "\U{0004}\0\U{0002}a\U{0002}aa");
expect r0 <==> isSubstringPred("\U{0002}a", "\U{0004}\0\U{0002}a\U{0002}aa");
expect r0 ==> isSubstringPred("\U{0002}a", "\U{0004}\0\U{0002}a\U{0002}aa");
expect isSubstringPred("\U{0002}a", "\U{0004}\0\U{0002}a\U{0002}aa") ==> r0;
expect isSubstringPred("\U{0002}a", "\U{0004}\0\U{0002}a\U{0002}aa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0002}a", "\U{0004}\0\U{0002}a\U{0002}aa");
}
method {:test} Test93() {
var r0 := isSubstring("\U{000C}\U{0004}aa\U{0008}\n\0", "\U{000E}\U{0002}\U{0006}a");
expect r0 <==> isSubstringPred("\U{000C}\U{0004}aa\U{0008}\n\0", "\U{000E}\U{0002}\U{0006}a");
expect r0 ==> isSubstringPred("\U{000C}\U{0004}aa\U{0008}\n\0", "\U{000E}\U{0002}\U{0006}a");
expect isSubstringPred("\U{000C}\U{0004}aa\U{0008}\n\0", "\U{000E}\U{0002}\U{0006}a") ==> r0;
expect isSubstringPred("\U{000C}\U{0004}aa\U{0008}\n\0", "\U{000E}\U{0002}\U{0006}a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{000C}\U{0004}aa\U{0008}\n\0", "\U{000E}\U{0002}\U{0006}a");
}
method {:test} Test94() {
var r0 := haveCommonKSubstring(26, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0008}a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(26, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0008}a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(26, "\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "\U{0008}a\0\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test95() {
var r0 := haveCommonKSubstring(103, "\U{0008}\U{0002}aaaaaaaaaaaaaaaaaaaa\0", "\naaaaaaaaaaaaaaaa\U{0004}aa\U{0006}aa");
expect r0 <==> haveCommonKSubstringPred(103, "\U{0008}\U{0002}aaaaaaaaaaaaaaaaaaaa\0", "\naaaaaaaaaaaaaaaa\U{0004}aa\U{0006}aa");
expect !r0 <==> haveNotCommonKSubstringPred(103, "\U{0008}\U{0002}aaaaaaaaaaaaaaaaaaaa\0", "\naaaaaaaaaaaaaaaa\U{0004}aa\U{0006}aa");
}
method {:test} Test96() {
expect |"\U{0002}aaaa\U{0004}\U{0006}a"| <= |"\U{0008}\0aaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0002}aaaa\U{0004}\U{0006}a", "\U{0008}\0aaaaaaa");
expect forall k :: r0 < k <= |"\U{0002}aaaa\U{0004}\U{0006}a"| ==> !haveCommonKSubstringPred(k, "\U{0002}aaaa\U{0004}\U{0006}a", "\U{0008}\0aaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0002}aaaa\U{0004}\U{0006}a", "\U{0008}\0aaaaaaa");
}

// REPEAT 4 - TIME: 99.9726535 s

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
var r0 := isSubstring("\U{0006}a\0a", "\U{0004}a\U{0002}\U{0006}a\0\U{0006}a\0aa");
expect r0 <==> isSubstringPred("\U{0006}a\0a", "\U{0004}a\U{0002}\U{0006}a\0\U{0006}a\0aa");
expect r0 ==> isSubstringPred("\U{0006}a\0a", "\U{0004}a\U{0002}\U{0006}a\0\U{0006}a\0aa");
expect isSubstringPred("\U{0006}a\0a", "\U{0004}a\U{0002}\U{0006}a\0\U{0006}a\0aa") ==> r0;
expect isSubstringPred("\U{0006}a\0a", "\U{0004}a\U{0002}\U{0006}a\0\U{0006}a\0aa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0006}a\0a", "\U{0004}a\U{0002}\U{0006}a\0\U{0006}a\0aa");
}
method {:test} Test100() {
var r0 := isSubstring("\U{0012}aaaa\U{000C}a\U{000E}aaaa\0\U{0006}aaa\na\U{0018}", "\U{001A}aaaaaa\U{0010}\U{0008}a\U{0004}\U{0014}aaaaa\U{0002}aaaa\U{0016}");
expect r0 <==> isSubstringPred("\U{0012}aaaa\U{000C}a\U{000E}aaaa\0\U{0006}aaa\na\U{0018}", "\U{001A}aaaaaa\U{0010}\U{0008}a\U{0004}\U{0014}aaaaa\U{0002}aaaa\U{0016}");
expect r0 ==> isSubstringPred("\U{0012}aaaa\U{000C}a\U{000E}aaaa\0\U{0006}aaa\na\U{0018}", "\U{001A}aaaaaa\U{0010}\U{0008}a\U{0004}\U{0014}aaaaa\U{0002}aaaa\U{0016}");
expect isSubstringPred("\U{0012}aaaa\U{000C}a\U{000E}aaaa\0\U{0006}aaa\na\U{0018}", "\U{001A}aaaaaa\U{0010}\U{0008}a\U{0004}\U{0014}aaaaa\U{0002}aaaa\U{0016}") ==> r0;
expect isSubstringPred("\U{0012}aaaa\U{000C}a\U{000E}aaaa\0\U{0006}aaa\na\U{0018}", "\U{001A}aaaaaa\U{0010}\U{0008}a\U{0004}\U{0014}aaaaa\U{0002}aaaa\U{0016}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0012}aaaa\U{000C}a\U{000E}aaaa\0\U{0006}aaa\na\U{0018}", "\U{001A}aaaaaa\U{0010}\U{0008}a\U{0004}\U{0014}aaaaa\U{0002}aaaa\U{0016}");
}
method {:test} Test101() {
var r0 := haveCommonKSubstring(27, "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "\n\U{0002}aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(27, "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "\n\U{0002}aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(27, "\U{0008}\0aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0006}", "\n\U{0002}aaaaaaa\U{0004}aaaaaaaaaaaaaaaaaaa");
}
method {:test} Test102() {
var r0 := haveCommonKSubstring(104, "\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0008}\U{0004}");
expect r0 <==> haveCommonKSubstringPred(104, "\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0008}\U{0004}");
expect !r0 <==> haveNotCommonKSubstringPred(104, "\U{0006}\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0008}\U{0004}");
}
method {:test} Test103() {
expect |"\naaaaaaa\U{0006}\U{0008}"| <= |"\0aaaaaa\U{0002}a\U{0004}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\naaaaaaa\U{0006}\U{0008}", "\0aaaaaa\U{0002}a\U{0004}aaa");
expect forall k :: r0 < k <= |"\naaaaaaa\U{0006}\U{0008}"| ==> !haveCommonKSubstringPred(k, "\naaaaaaa\U{0006}\U{0008}", "\0aaaaaa\U{0002}a\U{0004}aaa");
expect haveCommonKSubstringPred(r0, "\naaaaaaa\U{0006}\U{0008}", "\0aaaaaa\U{0002}a\U{0004}aaa");
}

// REPEAT 5 - TIME: 105.4365062 s

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
var r0 := isSubstring("\U{0006}\0a", "\U{0004}\U{0002}\U{0006}\0\U{0006}\0a");
expect r0 <==> isSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}\U{0006}\0\U{0006}\0a");
expect r0 ==> isSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}\U{0006}\0\U{0006}\0a");
expect isSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}\U{0006}\0\U{0006}\0a") ==> r0;
expect isSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}\U{0006}\0\U{0006}\0a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0006}\0a", "\U{0004}\U{0002}\U{0006}\0\U{0006}\0a");
}
method {:test} Test107() {
var r0 := isSubstring("aaaaaa\U{0008}aaaa\U{0010}a\U{0016}aaaaaaaaaa\U{000C}aa\U{0004}\U{001A}", "aaaaaaa\naaa\0a\U{0002}\U{0012}a\U{000E}\U{0018}aaaa\U{0006}\U{001C}\U{0014}aaa\U{001E}");
expect r0 <==> isSubstringPred("aaaaaa\U{0008}aaaa\U{0010}a\U{0016}aaaaaaaaaa\U{000C}aa\U{0004}\U{001A}", "aaaaaaa\naaa\0a\U{0002}\U{0012}a\U{000E}\U{0018}aaaa\U{0006}\U{001C}\U{0014}aaa\U{001E}");
expect r0 ==> isSubstringPred("aaaaaa\U{0008}aaaa\U{0010}a\U{0016}aaaaaaaaaa\U{000C}aa\U{0004}\U{001A}", "aaaaaaa\naaa\0a\U{0002}\U{0012}a\U{000E}\U{0018}aaaa\U{0006}\U{001C}\U{0014}aaa\U{001E}");
expect isSubstringPred("aaaaaa\U{0008}aaaa\U{0010}a\U{0016}aaaaaaaaaa\U{000C}aa\U{0004}\U{001A}", "aaaaaaa\naaa\0a\U{0002}\U{0012}a\U{000E}\U{0018}aaaa\U{0006}\U{001C}\U{0014}aaa\U{001E}") ==> r0;
expect isSubstringPred("aaaaaa\U{0008}aaaa\U{0010}a\U{0016}aaaaaaaaaa\U{000C}aa\U{0004}\U{001A}", "aaaaaaa\naaa\0a\U{0002}\U{0012}a\U{000E}\U{0018}aaaa\U{0006}\U{001C}\U{0014}aaa\U{001E}") ==> r0;
expect !r0 <==> isNotSubstringPred("aaaaaa\U{0008}aaaa\U{0010}a\U{0016}aaaaaaaaaa\U{000C}aa\U{0004}\U{001A}", "aaaaaaa\naaa\0a\U{0002}\U{0012}a\U{000E}\U{0018}aaaa\U{0006}\U{001C}\U{0014}aaa\U{001E}");
}
method {:test} Test108() {
var r0 := haveCommonKSubstring(28, "\U{000C}\naaa\U{0004}a\U{0002}aaaaaaaaaa\U{0008}aaaaa\U{0006}aa\0a", "\naaa\U{0004}a\U{0002}aaaaaaaaaa\U{0008}aaaaa\U{0006}aa\0a");
expect r0 <==> haveCommonKSubstringPred(28, "\U{000C}\naaa\U{0004}a\U{0002}aaaaaaaaaa\U{0008}aaaaa\U{0006}aa\0a", "\naaa\U{0004}a\U{0002}aaaaaaaaaa\U{0008}aaaaa\U{0006}aa\0a");
expect !r0 <==> haveNotCommonKSubstringPred(28, "\U{000C}\naaa\U{0004}a\U{0002}aaaaaaaaaa\U{0008}aaaaa\U{0006}aa\0a", "\naaa\U{0004}a\U{0002}aaaaaaaaaa\U{0008}aaaaa\U{0006}aa\0a");
}
method {:test} Test109() {
var r0 := haveCommonKSubstring(105, "\U{0006}\0\U{0002}aaa\U{0004}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(105, "\U{0006}\0\U{0002}aaa\U{0004}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(105, "\U{0006}\0\U{0002}aaa\U{0004}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test110() {
expect |"\U{0008}aa\0"| <= |"\U{0004}aa\U{0002}aaa\U{0006}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}aa\0", "\U{0004}aa\U{0002}aaa\U{0006}aaa");
expect forall k :: r0 < k <= |"\U{0008}aa\0"| ==> !haveCommonKSubstringPred(k, "\U{0008}aa\0", "\U{0004}aa\U{0002}aaa\U{0006}aaa");
expect haveCommonKSubstringPred(r0, "\U{0008}aa\0", "\U{0004}aa\U{0002}aaa\U{0006}aaa");
}

// REPEAT 6 - TIME: 110.4584875 s

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
var r0 := isSubstring("\U{0002}a", "\U{0004}\0a\U{0002}\U{0002}a");
expect r0 <==> isSubstringPred("\U{0002}a", "\U{0004}\0a\U{0002}\U{0002}a");
expect r0 ==> isSubstringPred("\U{0002}a", "\U{0004}\0a\U{0002}\U{0002}a");
expect isSubstringPred("\U{0002}a", "\U{0004}\0a\U{0002}\U{0002}a") ==> r0;
expect isSubstringPred("\U{0002}a", "\U{0004}\0a\U{0002}\U{0002}a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0002}a", "\U{0004}\0a\U{0002}\U{0002}a");
}
method {:test} Test114() {
var r0 := isSubstring("\U{0016}\U{0004}a\naaaa\U{0008}a\U{0010}aaaaaaaa\U{0012}aaaa\U{000C}aaaa\0", "\U{0014}\U{0002}a\U{0006}a\U{000E}");
expect r0 <==> isSubstringPred("\U{0016}\U{0004}a\naaaa\U{0008}a\U{0010}aaaaaaaa\U{0012}aaaa\U{000C}aaaa\0", "\U{0014}\U{0002}a\U{0006}a\U{000E}");
expect r0 ==> isSubstringPred("\U{0016}\U{0004}a\naaaa\U{0008}a\U{0010}aaaaaaaa\U{0012}aaaa\U{000C}aaaa\0", "\U{0014}\U{0002}a\U{0006}a\U{000E}");
expect isSubstringPred("\U{0016}\U{0004}a\naaaa\U{0008}a\U{0010}aaaaaaaa\U{0012}aaaa\U{000C}aaaa\0", "\U{0014}\U{0002}a\U{0006}a\U{000E}") ==> r0;
expect isSubstringPred("\U{0016}\U{0004}a\naaaa\U{0008}a\U{0010}aaaaaaaa\U{0012}aaaa\U{000C}aaaa\0", "\U{0014}\U{0002}a\U{0006}a\U{000E}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0016}\U{0004}a\naaaa\U{0008}a\U{0010}aaaaaaaa\U{0012}aaaa\U{000C}aaaa\0", "\U{0014}\U{0002}a\U{0006}a\U{000E}");
}
method {:test} Test115() {
var r0 := haveCommonKSubstring(29, "\U{0002}\U{0004}\U{0006}aaaaaaaaaaa\0aaaaaaaaaaaaaaa", "\U{0004}\U{0006}aaaaaaaaaaa\0aaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(29, "\U{0002}\U{0004}\U{0006}aaaaaaaaaaa\0aaaaaaaaaaaaaaa", "\U{0004}\U{0006}aaaaaaaaaaa\0aaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(29, "\U{0002}\U{0004}\U{0006}aaaaaaaaaaa\0aaaaaaaaaaaaaaa", "\U{0004}\U{0006}aaaaaaaaaaa\0aaaaaaaaaaaaaaa");
}
method {:test} Test116() {
var r0 := haveCommonKSubstring(106, "\U{0004}\0aaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(106, "\U{0004}\0aaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(106, "\U{0004}\0aaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test117() {
expect |"\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0"| <= |"\U{0004}aaaaa\U{0002}aa\U{0010}aaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0", "\U{0004}aaaaa\U{0002}aa\U{0010}aaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0"| ==> !haveCommonKSubstringPred(k, "\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0", "\U{0004}aaaaa\U{0002}aa\U{0010}aaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0008}aa\U{0006}a\na\U{000C}a\U{000E}aaaaaaaaaaaaa\U{0012}aa\0", "\U{0004}aaaaa\U{0002}aa\U{0010}aaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 7 - TIME: 115.817649 s

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
var r0 := isSubstring("\U{0006}\0aaa", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aaa");
expect r0 <==> isSubstringPred("\U{0006}\0aaa", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aaa");
expect r0 ==> isSubstringPred("\U{0006}\0aaa", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aaa");
expect isSubstringPred("\U{0006}\0aaa", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aaa") ==> r0;
expect isSubstringPred("\U{0006}\0aaa", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aaa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0006}\0aaa", "\U{0004}\U{0002}a\U{0006}\0\U{0006}\0aaa");
}
method {:test} Test121() {
var r0 := isSubstring("\U{0004}a", "\U{0006}\U{0002}a\0a");
expect r0 <==> isSubstringPred("\U{0004}a", "\U{0006}\U{0002}a\0a");
expect r0 ==> isSubstringPred("\U{0004}a", "\U{0006}\U{0002}a\0a");
expect isSubstringPred("\U{0004}a", "\U{0006}\U{0002}a\0a") ==> r0;
expect isSubstringPred("\U{0004}a", "\U{0006}\U{0002}a\0a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}a", "\U{0006}\U{0002}a\0a");
}
method {:test} Test122() {
var r0 := haveCommonKSubstring(30, "\U{0004}\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa", "\U{0004}\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(30, "\U{0004}\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa", "\U{0004}\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(30, "\U{0004}\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa", "\U{0004}\0aaaaaaaaa\U{0002}aaaaaaaaaaaaaaaaaa");
}
method {:test} Test123() {
var r0 := haveCommonKSubstring(107, "\n\U{0002}aaaaaaa\U{0006}a\U{0008}aaaaa", "\U{000C}aaaaaaaaaaaaaaaaaa\U{0004}aaaa\0");
expect r0 <==> haveCommonKSubstringPred(107, "\n\U{0002}aaaaaaa\U{0006}a\U{0008}aaaaa", "\U{000C}aaaaaaaaaaaaaaaaaa\U{0004}aaaa\0");
expect !r0 <==> haveNotCommonKSubstringPred(107, "\n\U{0002}aaaaaaa\U{0006}a\U{0008}aaaaa", "\U{000C}aaaaaaaaaaaaaaaaaa\U{0004}aaaa\0");
}
method {:test} Test124() {
expect |"\U{0004}aa\0"| <= |"\U{0002}aaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}aa\0", "\U{0002}aaaa");
expect forall k :: r0 < k <= |"\U{0004}aa\0"| ==> !haveCommonKSubstringPred(k, "\U{0004}aa\0", "\U{0002}aaaa");
expect haveCommonKSubstringPred(r0, "\U{0004}aa\0", "\U{0002}aaaa");
}

// REPEAT 8 - TIME: 121.6768802 s

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
var r0 := isSubstring("\U{0004}\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaa\U{0004}\0a\U{0004}\0aaaaaaaaa");
expect r0 <==> isSubstringPred("\U{0004}\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaa\U{0004}\0a\U{0004}\0aaaaaaaaa");
expect r0 ==> isSubstringPred("\U{0004}\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaa\U{0004}\0a\U{0004}\0aaaaaaaaa");
expect isSubstringPred("\U{0004}\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaa\U{0004}\0a\U{0004}\0aaaaaaaaa") ==> r0;
expect isSubstringPred("\U{0004}\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaa\U{0004}\0a\U{0004}\0aaaaaaaaa") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}\0aaaaaaaaa", "\U{0002}aaaaaaaaaaaa\U{0004}\0a\U{0004}\0aaaaaaaaa");
}
method {:test} Test128() {
var r0 := isSubstring("\U{0012}aaaa\U{0002}aaaaa\U{000C}aaaaaaaaaaaaa\U{000E}a\U{0004}aa", "\U{0010}aaaaaa\U{0006}aaaaa\U{0008}\0aa\n");
expect r0 <==> isSubstringPred("\U{0012}aaaa\U{0002}aaaaa\U{000C}aaaaaaaaaaaaa\U{000E}a\U{0004}aa", "\U{0010}aaaaaa\U{0006}aaaaa\U{0008}\0aa\n");
expect r0 ==> isSubstringPred("\U{0012}aaaa\U{0002}aaaaa\U{000C}aaaaaaaaaaaaa\U{000E}a\U{0004}aa", "\U{0010}aaaaaa\U{0006}aaaaa\U{0008}\0aa\n");
expect isSubstringPred("\U{0012}aaaa\U{0002}aaaaa\U{000C}aaaaaaaaaaaaa\U{000E}a\U{0004}aa", "\U{0010}aaaaaa\U{0006}aaaaa\U{0008}\0aa\n") ==> r0;
expect isSubstringPred("\U{0012}aaaa\U{0002}aaaaa\U{000C}aaaaaaaaaaaaa\U{000E}a\U{0004}aa", "\U{0010}aaaaaa\U{0006}aaaaa\U{0008}\0aa\n") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0012}aaaa\U{0002}aaaaa\U{000C}aaaaaaaaaaaaa\U{000E}a\U{0004}aa", "\U{0010}aaaaaa\U{0006}aaaaa\U{0008}\0aa\n");
}
method {:test} Test129() {
var r0 := haveCommonKSubstring(22, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(22, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(22, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}a\0aaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test130() {
var r0 := haveCommonKSubstring(108, "\U{0008}aaaaaaaaaaaaaaaa\0aaaaa\U{0004}aa", "\U{0006}aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa");
expect r0 <==> haveCommonKSubstringPred(108, "\U{0008}aaaaaaaaaaaaaaaa\0aaaaa\U{0004}aa", "\U{0006}aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa");
expect !r0 <==> haveNotCommonKSubstringPred(108, "\U{0008}aaaaaaaaaaaaaaaa\0aaaaa\U{0004}aa", "\U{0006}aaaaaaaaaaaaaaaaaaaaa\U{0002}aaaa");
}
method {:test} Test131() {
expect |"\U{0008}aaa\0a\U{0002}"| <= |"\naaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0008}aaa\0a\U{0002}", "\naaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
expect forall k :: r0 < k <= |"\U{0008}aaa\0a\U{0002}"| ==> !haveCommonKSubstringPred(k, "\U{0008}aaa\0a\U{0002}", "\naaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
expect haveCommonKSubstringPred(r0, "\U{0008}aaa\0a\U{0002}", "\naaaaa\U{0004}\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 9 - TIME: 127.3734055 s

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
var r0 := isSubstring("\U{0004}aaa\0a", "\U{0002}aaaaaa\U{0004}aaa\0aaa\U{0004}aaa\0a");
expect r0 <==> isSubstringPred("\U{0004}aaa\0a", "\U{0002}aaaaaa\U{0004}aaa\0aaa\U{0004}aaa\0a");
expect r0 ==> isSubstringPred("\U{0004}aaa\0a", "\U{0002}aaaaaa\U{0004}aaa\0aaa\U{0004}aaa\0a");
expect isSubstringPred("\U{0004}aaa\0a", "\U{0002}aaaaaa\U{0004}aaa\0aaa\U{0004}aaa\0a") ==> r0;
expect isSubstringPred("\U{0004}aaa\0a", "\U{0002}aaaaaa\U{0004}aaa\0aaa\U{0004}aaa\0a") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0004}aaa\0a", "\U{0002}aaaaaa\U{0004}aaa\0aaa\U{0004}aaa\0a");
}
method {:test} Test135() {
var r0 := isSubstring("\U{0012}aaaaaaaaaaaaaaaa\naaaaaaaaa\U{0010}a", "aaaa\U{0002}\U{0004}a\U{0008}aaaaaaaaa\U{000E}aaaaa\0aaaa\U{0006}\U{000C}");
expect r0 <==> isSubstringPred("\U{0012}aaaaaaaaaaaaaaaa\naaaaaaaaa\U{0010}a", "aaaa\U{0002}\U{0004}a\U{0008}aaaaaaaaa\U{000E}aaaaa\0aaaa\U{0006}\U{000C}");
expect r0 ==> isSubstringPred("\U{0012}aaaaaaaaaaaaaaaa\naaaaaaaaa\U{0010}a", "aaaa\U{0002}\U{0004}a\U{0008}aaaaaaaaa\U{000E}aaaaa\0aaaa\U{0006}\U{000C}");
expect isSubstringPred("\U{0012}aaaaaaaaaaaaaaaa\naaaaaaaaa\U{0010}a", "aaaa\U{0002}\U{0004}a\U{0008}aaaaaaaaa\U{000E}aaaaa\0aaaa\U{0006}\U{000C}") ==> r0;
expect isSubstringPred("\U{0012}aaaaaaaaaaaaaaaa\naaaaaaaaa\U{0010}a", "aaaa\U{0002}\U{0004}a\U{0008}aaaaaaaaa\U{000E}aaaaa\0aaaa\U{0006}\U{000C}") ==> r0;
expect !r0 <==> isNotSubstringPred("\U{0012}aaaaaaaaaaaaaaaa\naaaaaaaaa\U{0010}a", "aaaa\U{0002}\U{0004}a\U{0008}aaaaaaaaa\U{000E}aaaaa\0aaaa\U{0006}\U{000C}");
}
method {:test} Test136() {
var r0 := haveCommonKSubstring(2, "\U{0002}a\0aaaaaaaaaaaaaaaaaaaa", "\U{0004}aaa");
expect r0 <==> haveCommonKSubstringPred(2, "\U{0002}a\0aaaaaaaaaaaaaaaaaaaa", "\U{0004}aaa");
expect !r0 <==> haveNotCommonKSubstringPred(2, "\U{0002}a\0aaaaaaaaaaaaaaaaaaaa", "\U{0004}aaa");
}
method {:test} Test137() {
var r0 := haveCommonKSubstring(109, "\U{0008}aaaaaa\0aaaaaaaa\U{0002}\U{0004}aaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(109, "\U{0008}aaaaaa\0aaaaaaaa\U{0002}\U{0004}aaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
expect !r0 <==> haveNotCommonKSubstringPred(109, "\U{0008}aaaaaa\0aaaaaaaa\U{0002}\U{0004}aaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test138() {
expect |"\U{0004}a\0a"| <= |"\U{0002}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\U{0004}a\0a", "\U{0002}aaa");
expect forall k :: r0 < k <= |"\U{0004}a\0a"| ==> !haveCommonKSubstringPred(k, "\U{0004}a\0a", "\U{0002}aaa");
expect haveCommonKSubstringPred(r0, "\U{0004}a\0a", "\U{0002}aaa");
}

// REPEAT 10 - TIME: 133.1401635 s

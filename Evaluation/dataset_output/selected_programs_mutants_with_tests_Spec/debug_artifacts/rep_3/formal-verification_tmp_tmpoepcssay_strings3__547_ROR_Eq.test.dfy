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
  return |pre| == |str| && forall i :: 0 <= i < |pre| ==> pre[i] == str[i];
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

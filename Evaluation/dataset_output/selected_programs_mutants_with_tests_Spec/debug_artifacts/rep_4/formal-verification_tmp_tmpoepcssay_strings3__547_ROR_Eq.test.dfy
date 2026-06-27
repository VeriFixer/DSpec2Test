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

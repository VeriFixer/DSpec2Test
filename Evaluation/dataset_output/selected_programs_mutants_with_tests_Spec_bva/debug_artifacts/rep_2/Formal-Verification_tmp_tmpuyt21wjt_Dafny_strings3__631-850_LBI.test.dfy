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

method {:test} Test76() {
var r0 := isPrefix("\n\U{0004}\U{0006}aaaa\0a", "\U{0008}\U{0002}aaaaaa");
expect !r0 <==> isNotPrefixPred("\n\U{0004}\U{0006}aaaa\0a", "\U{0008}\U{0002}aaaaaa");
expect r0 <==> isPrefixPred("\n\U{0004}\U{0006}aaaa\0a", "\U{0008}\U{0002}aaaaaa");
}
method {:test} Test77() {
var r0 := isPrefix("\U{0004}\0", "\U{0004}\0a\U{0002}");
expect !r0 <==> isNotPrefixPred("\U{0004}\0", "\U{0004}\0a\U{0002}");
expect r0 <==> isPrefixPred("\U{0004}\0", "\U{0004}\0a\U{0002}");
}
method {:test} Test78() {
var r0 := isSubstring("\U{0004}aaaaaa\0", "\U{0006}\U{0002}\U{0004}aaaaaa\0");
expect r0 <==> isSubstringPred("\U{0004}aaaaaa\0", "\U{0006}\U{0002}\U{0004}aaaaaa\0");
}
method {:test} Test79() {
var r0 := isSubstring("\U{0004}\0a", "\U{0002}aa");
expect r0 <==> isSubstringPred("\U{0004}\0a", "\U{0002}aa");
}
method {:test} Test80() {
var r0 := haveCommonKSubstring(8, "\U{0008}aaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0006}aaaaaaaaaa\U{0004}aaaaaaaaa\0aaaaaaaa");
expect r0 <==> haveCommonKSubstringPred(8, "\U{0008}aaaaaaaaaaaaaaaaaaaa\U{0002}", "\U{0006}aaaaaaaaaa\U{0004}aaaaaaaaa\0aaaaaaaa");
}
method {:test} Test81() {
var r0 := haveCommonKSubstring(101, "\U{0008}\U{0002}\U{0004}", "\naaaaa\0\U{0006}");
expect r0 <==> haveCommonKSubstringPred(101, "\U{0008}\U{0002}\U{0004}", "\naaaaa\0\U{0006}");
}
method {:test} Test82() {
expect |"\na\U{0006}aa\0\U{0008}"| <= |"\U{0004}aa\U{0002}aaa"|, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := maxCommonSubstringLength("\na\U{0006}aa\0\U{0008}", "\U{0004}aa\U{0002}aaa");
expect forall k :: r0 < k <= |"\na\U{0006}aa\0\U{0008}"| ==> !haveCommonKSubstringPred(k, "\na\U{0006}aa\0\U{0008}", "\U{0004}aa\U{0002}aaa");
expect haveCommonKSubstringPred(r0, "\na\U{0006}aa\0\U{0008}", "\U{0004}aa\U{0002}aaa");
}

// REPEAT 2 - TIME: 70.9606194 s

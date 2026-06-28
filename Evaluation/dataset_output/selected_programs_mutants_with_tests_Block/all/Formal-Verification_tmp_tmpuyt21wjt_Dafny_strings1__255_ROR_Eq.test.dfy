// Formal-Verification_tmp_tmpuyt21wjt_Dafny_strings1.dfy

predicate isPrefixPredicate(pre: string, str: string)
{
  |str| >= |pre| &&
  pre <= str
}

method {:testEntry} isPrefix(pre: string, str: string) returns (res: bool)
  ensures |pre| > |str| ==> !res
  ensures res == isPrefixPredicate(pre, str)
{
  if |pre| == |str| {
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

predicate isSubstringPredicate(sub: string, str: string)
{
  |str| >= |sub| &&
  exists i :: 
    0 <= i <= |str| &&
    isPrefixPredicate(sub, str[i..])
}

method {:testEntry} isSubstring(sub: string, str: string) returns (res: bool)
  ensures res == isSubstringPredicate(sub, str)
{
  if |sub| > |str| {
    return false;
  }
  var i := |str| - |sub|;
  while i >= 0
    invariant i >= -1
    invariant forall j :: i < j <= |str| - |sub| ==> !isPrefixPredicate(sub, str[j..])
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

predicate haveCommonKSubstringPredicate(k: nat, str1: string, str2: string)
{
  |str1| >= k &&
  |str2| >= k &&
  exists i :: 
    0 <= i <= |str1| - k &&
    isSubstringPredicate(str1[i..][..k], str2)
}

method {:testEntry} haveCommonKSubstring(k: nat, str1: string, str2: string)
    returns (found: bool)
  ensures |str1| < k || |str2| < k ==> !found
  ensures haveCommonKSubstringPredicate(k, str1, str2) == found
{
  if |str1| < k || |str2| < k {
    return false;
  }
  var i := |str1| - k;
  while i >= 0
    invariant i >= -1
    invariant forall j :: i < j <= |str1| - k ==> !isSubstringPredicate(str1[j..][..k], str2)
    decreases i
  {
    var isSub := isSubstring(str1[i..][..k], str2);
    if isSub {
      return true;
    }
    i := i - 1;
  }
  return false;
}

predicate maxCommonSubstringPredicate(str1: string, str2: string, len: nat)
{
  forall k :: 
    len < k <= |str1| ==>
      !haveCommonKSubstringPredicate(k, str1, str2)
}

method {:testEntry} maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
  ensures len <= |str1| && len <= |str2|
  ensures len >= 0
  ensures maxCommonSubstringPredicate(str1, str2, len)
{
  var i := |str1|;
  while i > 0
    invariant i >= 0
    invariant forall j :: i < j <= |str1| ==> !haveCommonKSubstringPredicate(j, str1, str2)
    decreases i
  {
    var ans := haveCommonKSubstring(i, str1, str2);
    if ans {
      return i;
    }
    i := i - 1;
  }
  assert i == 0;
  return 0;
}


method {:test} Test0() {
var r0 := isPrefix("a", "a");
expect |"a"| > |"a"| ==> !r0;
expect r0 == isPrefixPredicate("a", "a");
}
method {:test} Test1() {
var r0 := isPrefix("aaaaaaaa\0", "aaaaaaaa\U{0002}");
expect |"aaaaaaaa\0"| > |"aaaaaaaa\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaa\0", "aaaaaaaa\U{0002}");
}
method {:test} Test2() {
var r0 := isPrefix("aa", "a");
expect |"aa"| > |"a"| ==> !r0;
expect r0 == isPrefixPredicate("aa", "a");
}
method {:test} Test3() {
var r0 := isSubstring("a", "a");
expect r0 == isSubstringPredicate("a", "a");
}
method {:test} Test4() {
var r0 := isSubstring("aaaaaaaaaa", "aaaaaaaaaaa");
expect r0 == isSubstringPredicate("aaaaaaaaaa", "aaaaaaaaaaa");
}
method {:test} Test5() {
var r0 := isSubstring("aa", "a");
expect r0 == isSubstringPredicate("aa", "a");
}
method {:test} Test6() {
var r0 := haveCommonKSubstring(1, "a", "a");
expect |"a"| < 1 || |"a"| < 1 ==> !r0;
expect haveCommonKSubstringPredicate(1, "a", "a") == r0;
}
method {:test} Test7() {
var r0 := haveCommonKSubstring(1, "aaaaaaaaaaa", "aaaaaaa");
expect |"aaaaaaaaaaa"| < 1 || |"aaaaaaa"| < 1 ==> !r0;
expect haveCommonKSubstringPredicate(1, "aaaaaaaaaaa", "aaaaaaa") == r0;
}
method {:test} Test8() {
var r0 := haveCommonKSubstring(2, "aa", "a");
expect |"aa"| < 2 || |"a"| < 2 ==> !r0;
expect haveCommonKSubstringPredicate(2, "aa", "a") == r0;
}
method {:test} Test9() {
var r0 := haveCommonKSubstring(2, "a", "");
expect |"a"| < 2 || |""| < 2 ==> !r0;
expect haveCommonKSubstringPredicate(2, "a", "") == r0;
}
method {:test} Test10() {
var r0 := maxCommonSubstringLength("a", "");
expect r0 <= |"a"| && r0 <= |""|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a", "", r0);
}
method {:test} Test13() {
var r0 := maxCommonSubstringLength("aa", "a");
expect r0 <= |"aa"| && r0 <= |"a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aa", "a", r0);
}

// REPEAT 1 - TIME: 9.045918 s

method {:test} Test14() {
var r0 := isPrefix("a\0aaaaa\U{0004}aaaaaaa\U{0002}", "a\0aaaaa\U{0004}aaaaaaa\U{0002}a");
expect |"a\0aaaaa\U{0004}aaaaaaa\U{0002}"| > |"a\0aaaaa\U{0004}aaaaaaa\U{0002}a"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaaaa\U{0004}aaaaaaa\U{0002}", "a\0aaaaa\U{0004}aaaaaaa\U{0002}a");
}
method {:test} Test15() {
var r0 := isPrefix("\U{0004}\U{0006}a\U{0002}", "\U{0004}\U{0006}a\0");
expect |"\U{0004}\U{0006}a\U{0002}"| > |"\U{0004}\U{0006}a\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\U{0006}a\U{0002}", "\U{0004}\U{0006}a\0");
}
method {:test} Test16() {
var r0 := isPrefix("a\0aaaaaaa\U{0002}\U{0004}", "aaaaaaaaa\U{0006}");
expect |"a\0aaaaaaa\U{0002}\U{0004}"| > |"aaaaaaaaa\U{0006}"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaaaaaa\U{0002}\U{0004}", "aaaaaaaaa\U{0006}");
}
method {:test} Test17() {
var r0 := isSubstring("aa\U{0002}", "\U{0004}\0a");
expect r0 == isSubstringPredicate("aa\U{0002}", "\U{0004}\0a");
}
method {:test} Test18() {
var r0 := isSubstring("", "aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("", "aaaaaaaaaaaa");
}
method {:test} Test19() {
var r0 := isSubstring("a\0a", "\U{0002}a");
expect r0 == isSubstringPredicate("a\0a", "\U{0002}a");
}
method {:test} Test20() {
var r0 := haveCommonKSubstring(3, "aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0006}", "a\0aaaaa\U{0004}");
expect |"aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0006}"| < 3 || |"a\0aaaaa\U{0004}"| < 3 ==> !r0;
expect haveCommonKSubstringPredicate(3, "aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaa\U{0006}", "a\0aaaaa\U{0004}") == r0;
}
method {:test} Test21() {
var r0 := haveCommonKSubstring(6, "aaaaaaaaaaaa", "aaaaaaaa");
expect |"aaaaaaaaaaaa"| < 6 || |"aaaaaaaa"| < 6 ==> !r0;
expect haveCommonKSubstringPredicate(6, "aaaaaaaaaaaa", "aaaaaaaa") == r0;
}
method {:test} Test22() {
var r0 := haveCommonKSubstring(9, "\U{0004}\U{0002}aaaaaaa", "aaaaaaa\0");
expect |"\U{0004}\U{0002}aaaaaaa"| < 9 || |"aaaaaaa\0"| < 9 ==> !r0;
expect haveCommonKSubstringPredicate(9, "\U{0004}\U{0002}aaaaaaa", "aaaaaaa\0") == r0;
}
method {:test} Test23() {
var r0 := haveCommonKSubstring(4, "a\0\U{0002}", "\U{0004}a");
expect |"a\0\U{0002}"| < 4 || |"\U{0004}a"| < 4 ==> !r0;
expect haveCommonKSubstringPredicate(4, "a\0\U{0002}", "\U{0004}a") == r0;
}
method {:test} Test24() {
var r0 := maxCommonSubstringLength("aa\0", "a\U{0002}");
expect r0 <= |"aa\0"| && r0 <= |"a\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aa\0", "a\U{0002}", r0);
}
method {:test} Test26() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaa\0", "a\U{0002}");
expect r0 <= |"aaaaaaaaaaaa\0"| && r0 <= |"a\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaa\0", "a\U{0002}", r0);
}
method {:test} Test27() {
var r0 := maxCommonSubstringLength("aaa", "a\0");
expect r0 <= |"aaa"| && r0 <= |"a\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaa", "a\0", r0);
}

// REPEAT 2 - TIME: 15.2707325 s

method {:test} Test28() {
var r0 := isPrefix("\0a", "\0a\U{0002}");
expect |"\0a"| > |"\0a\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("\0a", "\0a\U{0002}");
}
method {:test} Test29() {
var r0 := isPrefix("\U{0002}aa", "\U{0004}\0aaaaaaaa");
expect |"\U{0002}aa"| > |"\U{0004}\0aaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}aa", "\U{0004}\0aaaaaaaa");
}
method {:test} Test30() {
var r0 := isPrefix("\U{0004}\U{0002}aaaa", "\U{0006}\0aaa");
expect |"\U{0004}\U{0002}aaaa"| > |"\U{0006}\0aaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\U{0002}aaaa", "\U{0006}\0aaa");
}
method {:test} Test31() {
var r0 := isSubstring("\U{0008}\U{0002}\U{0004}", "\U{0006}\0aa");
expect r0 == isSubstringPredicate("\U{0008}\U{0002}\U{0004}", "\U{0006}\0aa");
}
method {:test} Test32() {
var r0 := isSubstring("a\0aaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaa\U{0004}a\0aaaaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("a\0aaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaa\U{0004}a\0aaaaaaaaaaaaaaa");
}
method {:test} Test33() {
var r0 := isSubstring("\U{0004}aa\U{0002}", "\U{0006}\0a");
expect r0 == isSubstringPredicate("\U{0004}aa\U{0002}", "\U{0006}\0a");
}
method {:test} Test34() {
var r0 := haveCommonKSubstring(10, "aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa\U{0004}a", "aaaaaaa\0aa");
expect |"aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| < 10 || |"aaaaaaa\0aa"| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "aaa\U{0002}aaaaaaaaaaaaaaaaaaaaaa\U{0004}a", "aaaaaaa\0aa") == r0;
}
method {:test} Test35() {
var r0 := haveCommonKSubstring(11, "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| < 11 || |"aaaaaaaaaaaaaaaaa"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test36() {
var r0 := haveCommonKSubstring(10, "\U{0008}a\U{0002}aaaaaaa", "a\0aaaaa\U{0004}\U{0006}");
expect |"\U{0008}a\U{0002}aaaaaaa"| < 10 || |"a\0aaaaa\U{0004}\U{0006}"| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "\U{0008}a\U{0002}aaaaaaa", "a\0aaaaa\U{0004}\U{0006}") == r0;
}
method {:test} Test37() {
var r0 := haveCommonKSubstring(10, "\U{0002}\0a\U{0004}", "\U{0006}aa");
expect |"\U{0002}\0a\U{0004}"| < 10 || |"\U{0006}aa"| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "\U{0002}\0a\U{0004}", "\U{0006}aa") == r0;
}
method {:test} Test38() {
var r0 := maxCommonSubstringLength("\U{0002}\0aa", "aaa");
expect r0 <= |"\U{0002}\0aa"| && r0 <= |"aaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}\0aa", "aaa", r0);
}
method {:test} Test40() {
var r0 := maxCommonSubstringLength("\U{0004}\0a\U{0008}", "\U{0002}aaaaaaaaaaaaaaa\U{0006}");
expect r0 <= |"\U{0004}\0a\U{0008}"| && r0 <= |"\U{0002}aaaaaaaaaaaaaaa\U{0006}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}\0a\U{0008}", "\U{0002}aaaaaaaaaaaaaaa\U{0006}", r0);
}
method {:test} Test41() {
var r0 := maxCommonSubstringLength("\U{0004}aa\U{0006}\0aaaaaaaa\U{0008}", "a\U{0002}a");
expect r0 <= |"\U{0004}aa\U{0006}\0aaaaaaaa\U{0008}"| && r0 <= |"a\U{0002}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}aa\U{0006}\0aaaaaaaa\U{0008}", "a\U{0002}a", r0);
}

// REPEAT 3 - TIME: 21.3352582 s

method {:test} Test42() {
var r0 := isPrefix("\0a", "\0a\U{0002}a");
expect |"\0a"| > |"\0a\U{0002}a"| ==> !r0;
expect r0 == isPrefixPredicate("\0a", "\0a\U{0002}a");
}
method {:test} Test43() {
var r0 := isPrefix("\0\U{0002}aa\U{000C}a\U{0004}\U{0010}", "\U{0006}aa\naa\U{0008}\U{000E}");
expect |"\0\U{0002}aa\U{000C}a\U{0004}\U{0010}"| > |"\U{0006}aa\naa\U{0008}\U{000E}"| ==> !r0;
expect r0 == isPrefixPredicate("\0\U{0002}aa\U{000C}a\U{0004}\U{0010}", "\U{0006}aa\naa\U{0008}\U{000E}");
}
method {:test} Test44() {
var r0 := isPrefix("\naaaaaa\U{0004}aaa\U{0002}a\U{0008}aaa", "\U{000C}\0aaaaaaa\U{0006}a");
expect |"\naaaaaa\U{0004}aaa\U{0002}a\U{0008}aaa"| > |"\U{000C}\0aaaaaaa\U{0006}a"| ==> !r0;
expect r0 == isPrefixPredicate("\naaaaaa\U{0004}aaa\U{0002}a\U{0008}aaa", "\U{000C}\0aaaaaaa\U{0006}a");
}
method {:test} Test45() {
var r0 := isSubstring("\U{0002}aaaaaaa\U{0006}a\U{0008}aaaaaa\U{000E}", "\U{0010}\0a\naaaa\U{0004}aaaa\U{000C}aaaa");
expect r0 == isSubstringPredicate("\U{0002}aaaaaaa\U{0006}a\U{0008}aaaaaa\U{000E}", "\U{0010}\0a\naaaa\U{0004}aaaa\U{000C}aaaa");
}
method {:test} Test46() {
var r0 := isSubstring("aaaaaaaaaaaaaaa", "\U{0004}a\0aaaaaaa\U{0002}aaaaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("aaaaaaaaaaaaaaa", "\U{0004}a\0aaaaaaa\U{0002}aaaaaaaaaaaaaaa");
}
method {:test} Test47() {
var r0 := isSubstring("\U{0004}a\U{0002}\U{0008}aaaaaa\U{000C}", "\n\0a\U{0006}");
expect r0 == isSubstringPredicate("\U{0004}a\U{0002}\U{0008}aaaaaa\U{000C}", "\n\0a\U{0006}");
}
method {:test} Test48() {
var r0 := haveCommonKSubstring(12, "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\0", "aaaaaaaaaaaaaaaaa\U{0002}");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\0"| < 12 || |"aaaaaaaaaaaaaaaaa\U{0002}"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}\0", "aaaaaaaaaaaaaaaaa\U{0002}") == r0;
}
method {:test} Test49() {
var r0 := haveCommonKSubstring(12, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| < 12 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test50() {
var r0 := haveCommonKSubstring(12, "\U{000E}\U{0002}a\U{0006}aaaaa\U{000C}\U{0004}\U{0008}", "\U{0010}aaaaaa\0\n");
expect |"\U{000E}\U{0002}a\U{0006}aaaaa\U{000C}\U{0004}\U{0008}"| < 12 || |"\U{0010}aaaaaa\0\n"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "\U{000E}\U{0002}a\U{0006}aaaaa\U{000C}\U{0004}\U{0008}", "\U{0010}aaaaaa\0\n") == r0;
}
method {:test} Test51() {
var r0 := haveCommonKSubstring(12, "\n\U{0002}a\U{0004}aaa\U{0006}a", "\U{0008}aaaaaaaaa\0");
expect |"\n\U{0002}a\U{0004}aaa\U{0006}a"| < 12 || |"\U{0008}aaaaaaaaa\0"| < 12 ==> !r0;
expect haveCommonKSubstringPredicate(12, "\n\U{0002}a\U{0004}aaa\U{0006}a", "\U{0008}aaaaaaaaa\0") == r0;
}
method {:test} Test52() {
var r0 := maxCommonSubstringLength("a\U{0002}a\U{0008}aaaaaaa\U{0004}a\n\U{000C}", "\U{0006}\0");
expect r0 <= |"a\U{0002}a\U{0008}aaaaaaa\U{0004}a\n\U{000C}"| && r0 <= |"\U{0006}\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\U{0002}a\U{0008}aaaaaaa\U{0004}a\n\U{000C}", "\U{0006}\0", r0);
}
method {:test} Test54() {
var r0 := maxCommonSubstringLength("", "\U{0002}\0");
expect r0 <= |""| && r0 <= |"\U{0002}\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("", "\U{0002}\0", r0);
}
method {:test} Test55() {
var r0 := maxCommonSubstringLength("\U{0004}\0a\U{0008}\U{000C}aaaaa\naa\U{000E}a", "\U{0006}a\U{0002}");
expect r0 <= |"\U{0004}\0a\U{0008}\U{000C}aaaaa\naa\U{000E}a"| && r0 <= |"\U{0006}a\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}\0a\U{0008}\U{000C}aaaaa\naa\U{000E}a", "\U{0006}a\U{0002}", r0);
}

// REPEAT 4 - TIME: 28.535649 s

method {:test} Test56() {
var r0 := isPrefix("\U{0004}\0aaa", "\U{0004}\0aaa\U{0002}aaaaa");
expect |"\U{0004}\0aaa"| > |"\U{0004}\0aaa\U{0002}aaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0aaa", "\U{0004}\0aaa\U{0002}aaaaa");
}
method {:test} Test57() {
var r0 := isPrefix("\U{0006}\U{0002}a\U{0004}a", "\n\0aaa\U{0008}");
expect |"\U{0006}\U{0002}a\U{0004}a"| > |"\n\0aaa\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\U{0002}a\U{0004}a", "\n\0aaa\U{0008}");
}
method {:test} Test58() {
var r0 := isPrefix("\U{0008}a\U{0002}a\U{0004}a\U{0006}", "\n\0");
expect |"\U{0008}a\U{0002}a\U{0004}a\U{0006}"| > |"\n\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}a\U{0002}a\U{0004}a\U{0006}", "\n\0");
}
method {:test} Test59() {
var r0 := isSubstring("\U{0006}aa\U{0004}a\U{0002}a\n", "\U{0010}\0a\U{0008}a\U{000E}aaa\U{000C}aaaaaa");
expect r0 == isSubstringPredicate("\U{0006}aa\U{0004}a\U{0002}a\n", "\U{0010}\0a\U{0008}a\U{000E}aaa\U{000C}aaaaaa");
}
method {:test} Test60() {
var r0 := isSubstring("\U{0010}a\U{0004}\naaa\U{0002}a\U{000C}a\U{0008}", "\U{000E}\0aa\U{0006}\U{0010}a\U{0004}\naaa\U{0002}a\U{000C}a\U{0008}");
expect r0 == isSubstringPredicate("\U{0010}a\U{0004}\naaa\U{0002}a\U{000C}a\U{0008}", "\U{000E}\0aa\U{0006}\U{0010}a\U{0004}\naaa\U{0002}a\U{000C}a\U{0008}");
}
method {:test} Test61() {
var r0 := isSubstring("\U{0006}aa\U{0002}\n\U{0004}", "\U{000C}\0a\U{0008}a");
expect r0 == isSubstringPredicate("\U{0006}aa\U{0002}\n\U{0004}", "\U{000C}\0a\U{0008}a");
}
method {:test} Test62() {
var r0 := haveCommonKSubstring(13, "aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| < 13 || |"\0aaaaaaaaaaaaaaaaaa"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "aaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test63() {
var r0 := haveCommonKSubstring(16, "aaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| < 16 || |"aaaaaaaaaaaaaaaaaaa"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "aaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test64() {
var r0 := haveCommonKSubstring(19, "\U{0010}aaaaaaaaaaaaa\U{000C}aaaaaaaa\U{0002}a\naa\U{0008}a", "\U{000E}\0a\U{0004}aaaaaaaaaaaaa\U{0006}");
expect |"\U{0010}aaaaaaaaaaaaa\U{000C}aaaaaaaa\U{0002}a\naa\U{0008}a"| < 19 || |"\U{000E}\0a\U{0004}aaaaaaaaaaaaa\U{0006}"| < 19 ==> !r0;
expect haveCommonKSubstringPredicate(19, "\U{0010}aaaaaaaaaaaaa\U{000C}aaaaaaaa\U{0002}a\naa\U{0008}a", "\U{000E}\0a\U{0004}aaaaaaaaaaaaa\U{0006}") == r0;
}
method {:test} Test65() {
var r0 := haveCommonKSubstring(31, "\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}", "\U{000E}\0a\U{0008}aaa\n\U{0002}aaaaaaaaaa");
expect |"\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}"| < 31 || |"\U{000E}\0a\U{0008}aaa\n\U{0002}aaaaaaaaaa"| < 31 ==> !r0;
expect haveCommonKSubstringPredicate(31, "\U{000C}aaaaaaaaaaaaaaaaaa\U{0006}aaaaaa\U{0004}", "\U{000E}\0a\U{0008}aaa\n\U{0002}aaaaaaaaaa") == r0;
}
method {:test} Test66() {
var r0 := maxCommonSubstringLength("a\0aaaa\U{0006}\U{0004}aaaaa\U{0008}a\n", "aaa\U{0002}");
expect r0 <= |"a\0aaaa\U{0006}\U{0004}aaaaa\U{0008}a\n"| && r0 <= |"aaa\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0aaaa\U{0006}\U{0004}aaaaa\U{0008}a\n", "aaa\U{0002}", r0);
}
method {:test} Test68() {
var r0 := maxCommonSubstringLength("\U{0002}aaaaaa\U{0008}aaaaa\n\U{0006}\U{000C}", "\0aa\U{0004}");
expect r0 <= |"\U{0002}aaaaaa\U{0008}aaaaa\n\U{0006}\U{000C}"| && r0 <= |"\0aa\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}aaaaaa\U{0008}aaaaa\n\U{0006}\U{000C}", "\0aa\U{0004}", r0);
}
method {:test} Test69() {
var r0 := maxCommonSubstringLength("\n\0a\U{0004}\U{0008}", "aa\U{0002}\U{0006}");
expect r0 <= |"\n\0a\U{0004}\U{0008}"| && r0 <= |"aa\U{0002}\U{0006}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\n\0a\U{0004}\U{0008}", "aa\U{0002}\U{0006}", r0);
}

// REPEAT 5 - TIME: 35.8032619 s

method {:test} Test70() {
var r0 := isPrefix("\U{0004}a\0\U{0006}aaa\n\U{0002}\U{000C}", "\U{0004}a\0\U{0006}aaa\n\U{0002}\U{000C}\U{000E}\U{0008}aa");
expect |"\U{0004}a\0\U{0006}aaa\n\U{0002}\U{000C}"| > |"\U{0004}a\0\U{0006}aaa\n\U{0002}\U{000C}\U{000E}\U{0008}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}a\0\U{0006}aaa\n\U{0002}\U{000C}", "\U{0004}a\0\U{0006}aaa\n\U{0002}\U{000C}\U{000E}\U{0008}aa");
}
method {:test} Test71() {
var r0 := isPrefix("\U{0002}\0aaaaaa\U{000C}\U{000E}a\U{0010}", "\U{0004}aaaaaa\U{0008}a\U{0006}a\n");
expect |"\U{0002}\0aaaaaa\U{000C}\U{000E}a\U{0010}"| > |"\U{0004}aaaaaa\U{0008}a\U{0006}a\n"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0aaaaaa\U{000C}\U{000E}a\U{0010}", "\U{0004}aaaaaa\U{0008}a\U{0006}a\n");
}
method {:test} Test72() {
var r0 := isPrefix("\n\U{0002}a\U{0006}aa", "\U{0008}\0aa\U{0004}");
expect |"\n\U{0002}a\U{0006}aa"| > |"\U{0008}\0aa\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\n\U{0002}a\U{0006}aa", "\U{0008}\0aa\U{0004}");
}
method {:test} Test73() {
var r0 := isSubstring("\U{0006}aaaaaa\U{0002}a", "\U{0004}\0aaaaaaa");
expect r0 == isSubstringPredicate("\U{0006}aaaaaa\U{0002}a", "\U{0004}\0aaaaaaa");
}
method {:test} Test74() {
var r0 := isSubstring("\U{0014}\U{0002}aaaaaa\U{0004}aa\U{000E}\U{0012}a", "\U{0016}\0a\U{0006}a\U{000C}aa\na\U{0008}\U{0010}aa\U{0014}\U{0002}aaaaaa\U{0004}aa\U{000E}\U{0012}aa");
expect r0 == isSubstringPredicate("\U{0014}\U{0002}aaaaaa\U{0004}aa\U{000E}\U{0012}a", "\U{0016}\0a\U{0006}a\U{000C}aa\na\U{0008}\U{0010}aa\U{0014}\U{0002}aaaaaa\U{0004}aa\U{000E}\U{0012}aa");
}
method {:test} Test75() {
var r0 := isSubstring("\U{000E}aa\U{0004}\U{0008}a\U{0002}a\n", "\U{000C}\0aa\U{0006}a");
expect r0 == isSubstringPredicate("\U{000E}aa\U{0004}\U{0008}a\U{0002}a\n", "\U{000C}\0aa\U{0006}a");
}
method {:test} Test76() {
var r0 := haveCommonKSubstring(20, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaa"| < 20 || |"aaaaaaaaaaaaaaaaaaaa"| < 20 ==> !r0;
expect haveCommonKSubstringPredicate(20, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test77() {
var r0 := haveCommonKSubstring(20, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaa"| < 20 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 20 ==> !r0;
expect haveCommonKSubstringPredicate(20, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test78() {
var r0 := haveCommonKSubstring(20, "\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaaaa", "\U{0004}\0");
expect |"\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaaaa"| < 20 || |"\U{0004}\0"| < 20 ==> !r0;
expect haveCommonKSubstringPredicate(20, "\U{0006}aaaaaaaaaaaa\U{0002}aaaaaaaaaaaa", "\U{0004}\0") == r0;
}
method {:test} Test79() {
var r0 := haveCommonKSubstring(32, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 32 || |"\U{0002}aaaaaaaaaaaaaaaaa"| < 32 ==> !r0;
expect haveCommonKSubstringPredicate(32, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test80() {
var r0 := maxCommonSubstringLength("\U{000E}aaaaaa\U{0008}aa\U{0014}a\U{0012}\U{0018}a\U{0016}\U{001A}", "\U{000C}\U{0002}a\na\U{0010}\U{0004}\U{0006}aaaaa\0aaa\U{001C}");
expect r0 <= |"\U{000E}aaaaaa\U{0008}aa\U{0014}a\U{0012}\U{0018}a\U{0016}\U{001A}"| && r0 <= |"\U{000C}\U{0002}a\na\U{0010}\U{0004}\U{0006}aaaaa\0aaa\U{001C}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{000E}aaaaaa\U{0008}aa\U{0014}a\U{0012}\U{0018}a\U{0016}\U{001A}", "\U{000C}\U{0002}a\na\U{0010}\U{0004}\U{0006}aaaaa\0aaa\U{001C}", r0);
}
method {:test} Test81() {
var r0 := maxCommonSubstringLength("\U{000E}aaaa\U{0016}a\U{0008}aa\U{0014}aa\U{0018}a\U{0012}\U{001A}", "\U{000C}\U{0002}a\n\U{0004}aa\U{0006}\U{0010}aaaa\0aaa\U{001C}");
expect r0 <= |"\U{000E}aaaa\U{0016}a\U{0008}aa\U{0014}aa\U{0018}a\U{0012}\U{001A}"| && r0 <= |"\U{000C}\U{0002}a\n\U{0004}aa\U{0006}\U{0010}aaaa\0aaa\U{001C}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{000E}aaaa\U{0016}a\U{0008}aa\U{0014}aa\U{0018}a\U{0012}\U{001A}", "\U{000C}\U{0002}a\n\U{0004}aa\U{0006}\U{0010}aaaa\0aaa\U{001C}", r0);
}
method {:test} Test82() {
var r0 := maxCommonSubstringLength("\U{000C}\0a\U{0002}\U{0008}", "\U{0006}aaa\U{0004}\n");
expect r0 <= |"\U{000C}\0a\U{0002}\U{0008}"| && r0 <= |"\U{0006}aaa\U{0004}\n"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{000C}\0a\U{0002}\U{0008}", "\U{0006}aaa\U{0004}\n", r0);
}
method {:test} Test83() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaa\U{0002}\U{0008}a\n\U{000C}", "aa\0\U{0006}\U{0004}");
expect r0 <= |"aaaaaaaaaaaa\U{0002}\U{0008}a\n\U{000C}"| && r0 <= |"aa\0\U{0006}\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaa\U{0002}\U{0008}a\n\U{000C}", "aa\0\U{0006}\U{0004}", r0);
}

// REPEAT 6 - TIME: 43.5981982 s

method {:test} Test84() {
var r0 := isPrefix("\U{0002}\0a", "\U{0002}\0a\U{0004}");
expect |"\U{0002}\0a"| > |"\U{0002}\0a\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0a", "\U{0002}\0a\U{0004}");
}
method {:test} Test85() {
var r0 := isPrefix("\U{0006}aa\U{0002}", "\U{0004}aa\0");
expect |"\U{0006}aa\U{0002}"| > |"\U{0004}aa\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}aa\U{0002}", "\U{0004}aa\0");
}
method {:test} Test86() {
var r0 := isPrefix("\U{0004}aaaa\U{000C}a\U{0010}aaa\U{001A}a\U{0012}aa\U{001C} \U{0002}", "\U{000E}\0a\U{0008}aa\n\U{0006}a\U{0016}aaaaa\U{0014}\U{0018}\U{001E}");
expect |"\U{0004}aaaa\U{000C}a\U{0010}aaa\U{001A}a\U{0012}aa\U{001C} \U{0002}"| > |"\U{000E}\0a\U{0008}aa\n\U{0006}a\U{0016}aaaaa\U{0014}\U{0018}\U{001E}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}aaaa\U{000C}a\U{0010}aaa\U{001A}a\U{0012}aa\U{001C} \U{0002}", "\U{000E}\0a\U{0008}aa\n\U{0006}a\U{0016}aaaaa\U{0014}\U{0018}\U{001E}");
}
method {:test} Test87() {
var r0 := isSubstring("\naaaa", "\U{000C}aa\0\U{0004}\U{0006}aaa\U{0008}a\U{0002}aaaaaa");
expect r0 == isSubstringPredicate("\naaaa", "\U{000C}aa\0\U{0004}\U{0006}aaa\U{0008}a\U{0002}aaaaaa");
}
method {:test} Test88() {
var r0 := isSubstring("\U{0012}aaaaaaa\U{0006}\U{0008}aa\n\U{000C}a\U{000E}", "\U{0014}aaa\0\U{0004}aaa\U{0002}\U{0012}aaaaaaa\U{0006}\U{0008}aa\n\U{000C}a\U{000E}aaa\U{0010}");
expect r0 == isSubstringPredicate("\U{0012}aaaaaaa\U{0006}\U{0008}aa\n\U{000C}a\U{000E}", "\U{0014}aaa\0\U{0004}aaa\U{0002}\U{0012}aaaaaaa\U{0006}\U{0008}aa\n\U{000C}a\U{000E}aaa\U{0010}");
}
method {:test} Test89() {
var r0 := isSubstring("aaaaaaaaaaa\U{000C}aaa\U{0010}a\U{0004}a\U{000E}aaaaa\U{0008}aa", "\U{0016}aaaa\U{0002}aaa\naaa\U{0006}aaa\U{0012}aa\0aaaaa\U{0014}");
expect r0 == isSubstringPredicate("aaaaaaaaaaa\U{000C}aaa\U{0010}a\U{0004}a\U{000E}aaaaa\U{0008}aa", "\U{0016}aaaa\U{0002}aaa\naaa\U{0006}aaa\U{0012}aa\0aaaaa\U{0014}");
}
method {:test} Test90() {
var r0 := haveCommonKSubstring(21, "aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaa"| < 21 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 21 ==> !r0;
expect haveCommonKSubstringPredicate(21, "aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test91() {
var r0 := haveCommonKSubstring(22, "aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaa"| < 22 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 22 ==> !r0;
expect haveCommonKSubstringPredicate(22, "aaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test92() {
var r0 := haveCommonKSubstring(21, "\U{0006}aaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}");
expect |"\U{0006}aaaaaaaaaaaaaaaaaaaa"| < 21 || |"\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}"| < 21 ==> !r0;
expect haveCommonKSubstringPredicate(21, "\U{0006}aaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaa\0\U{0002}") == r0;
}
method {:test} Test93() {
var r0 := haveCommonKSubstring(33, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaa\0\U{0004}aaaaaaa\U{0006}\U{0002}");
expect |"\U{0008}aaaaaaaaaaaaaaaaaaaaaaa"| < 33 || |"aaaaaaaaaaaaaaaaaa\0\U{0004}aaaaaaa\U{0006}\U{0002}"| < 33 ==> !r0;
expect haveCommonKSubstringPredicate(33, "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaa\0\U{0004}aaaaaaa\U{0006}\U{0002}") == r0;
}
method {:test} Test94() {
var r0 := maxCommonSubstringLength("\U{0008}aaaaaaaaaaaaaaaaa", "\U{0006}aa\U{0004}aaaaa\0\U{0002}aaaaaaaa");
expect r0 <= |"\U{0008}aaaaaaaaaaaaaaaaa"| && r0 <= |"\U{0006}aa\U{0004}aaaaa\0\U{0002}aaaaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0008}aaaaaaaaaaaaaaaaa", "\U{0006}aa\U{0004}aaaaa\0\U{0002}aaaaaaaa", r0);
}
method {:test} Test96() {
var r0 := maxCommonSubstringLength("\0\U{0004}a", "\U{0002}a");
expect r0 <= |"\0\U{0004}a"| && r0 <= |"\U{0002}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\0\U{0004}a", "\U{0002}a", r0);
}
method {:test} Test97() {
var r0 := maxCommonSubstringLength("\U{0004}aaaaaaaaaaaaa", "\U{0002}aa\0a");
expect r0 <= |"\U{0004}aaaaaaaaaaaaa"| && r0 <= |"\U{0002}aa\0a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}aaaaaaaaaaaaa", "\U{0002}aa\0a", r0);
}

// REPEAT 7 - TIME: 52.3735216 s

method {:test} Test98() {
var r0 := isPrefix("\U{0004}\0aaa", "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa");
expect |"\U{0004}\0aaa"| > |"\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0aaa", "\U{0004}\0aaa\U{0002}aaaaaaaaaaaaa");
}
method {:test} Test99() {
var r0 := isPrefix("\U{0014}aaaaaaa\U{000C}a\U{0004}a\U{0002}", "\U{0016}aaa\0\U{0006}a\U{0008}aa\U{000E}\U{0010}\U{0012}\na");
expect |"\U{0014}aaaaaaa\U{000C}a\U{0004}a\U{0002}"| > |"\U{0016}aaa\0\U{0006}a\U{0008}aa\U{000E}\U{0010}\U{0012}\na"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0014}aaaaaaa\U{000C}a\U{0004}a\U{0002}", "\U{0016}aaa\0\U{0006}a\U{0008}aa\U{000E}\U{0010}\U{0012}\na");
}
method {:test} Test100() {
var r0 := isPrefix("\U{0012}aaaa\U{0006}\n\U{000E}a\U{0004}aaaa\U{0008}aaaaa", "\U{0010}\0aaa\U{0002}\U{000C}");
expect |"\U{0012}aaaa\U{0006}\n\U{000E}a\U{0004}aaaa\U{0008}aaaaa"| > |"\U{0010}\0aaa\U{0002}\U{000C}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0012}aaaa\U{0006}\n\U{000E}a\U{0004}aaaa\U{0008}aaaaa", "\U{0010}\0aaa\U{0002}\U{000C}");
}
method {:test} Test101() {
var r0 := isSubstring("aaaaa\U{0002}aaa\U{0008}aaaa\U{0004}\U{000C}aaa\na\U{0010}aaaaa", "aaaaaaaaaaaaaa\U{0006}aa\U{000E}\U{0014}aa\0aaaa\U{0016}\U{0012}");
expect r0 == isSubstringPredicate("aaaaa\U{0002}aaa\U{0008}aaaa\U{0004}\U{000C}aaa\na\U{0010}aaaaa", "aaaaaaaaaaaaaa\U{0006}aa\U{000E}\U{0014}aa\0aaaa\U{0016}\U{0012}");
}
method {:test} Test102() {
var r0 := isSubstring("\U{0004}a\U{0008}aaaa", "\U{0006}aaaa\0\U{0002}\U{0004}a\U{0008}aaaa");
expect r0 == isSubstringPredicate("\U{0004}a\U{0008}aaaa", "\U{0006}aaaa\0\U{0002}\U{0004}a\U{0008}aaaa");
}
method {:test} Test103() {
var r0 := isSubstring("aaaaaaaaaaaaaaa\U{0004}aaaaaa\0aaa\U{0008}\U{0002}\U{000C}", "\U{000E}aaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\na");
expect r0 == isSubstringPredicate("aaaaaaaaaaaaaaa\U{0004}aaaaaa\0aaa\U{0008}\U{0002}\U{000C}", "\U{000E}aaaaaaaaaaaaaaaa\U{0006}aaaaaaaa\na");
}
method {:test} Test104() {
var r0 := haveCommonKSubstring(23, "aaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaa"| < 23 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 23 ==> !r0;
expect haveCommonKSubstringPredicate(23, "aaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test105() {
var r0 := haveCommonKSubstring(26, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 26 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 26 ==> !r0;
expect haveCommonKSubstringPredicate(26, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test106() {
var r0 := haveCommonKSubstring(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa"| < 23 || |"\0aaaaaaaaaaaaaaaaaaaa"| < 23 ==> !r0;
expect haveCommonKSubstringPredicate(23, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test107() {
var r0 := haveCommonKSubstring(34, "\U{0004}aaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa\0");
expect |"\U{0004}aaaaaaaaaaaa"| < 34 || |"\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa\0"| < 34 ==> !r0;
expect haveCommonKSubstringPredicate(34, "\U{0004}aaaaaaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaa\U{0002}aaaaaa\0") == r0;
}
method {:test} Test108() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaa\U{0002}a\U{0004}\U{0006}\U{0008}a", "aaaaaaaaaaaaaaa\0a\naa");
expect r0 <= |"aaaaaaaaaaaaa\U{0002}a\U{0004}\U{0006}\U{0008}a"| && r0 <= |"aaaaaaaaaaaaaaa\0a\naa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaa\U{0002}a\U{0004}\U{0006}\U{0008}a", "aaaaaaaaaaaaaaa\0a\naa", r0);
}
method {:test} Test110() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{0006}", "aaa\0aaaaaaaaaaaaa\n\U{0002}a");
expect r0 <= |"aaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{0006}"| && r0 <= |"aaa\0aaaaaaaaaaaaa\n\U{0002}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaaa\U{0004}\U{0008}a\U{0006}", "aaa\0aaaaaaaaaaaaa\n\U{0002}a", r0);
}
method {:test} Test111() {
var r0 := maxCommonSubstringLength("aaa\0\U{0002}aaaaaaaaaaaaaaaaaa", "aaaaa\U{0004}aaaaaaaaaaa\U{0006}aa");
expect r0 <= |"aaa\0\U{0002}aaaaaaaaaaaaaaaaaa"| && r0 <= |"aaaaa\U{0004}aaaaaaaaaaa\U{0006}aa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaa\0\U{0002}aaaaaaaaaaaaaaaaaa", "aaaaa\U{0004}aaaaaaaaaaa\U{0006}aa", r0);
}

// REPEAT 8 - TIME: 62.4334235 s

method {:test} Test112() {
var r0 := isPrefix("aaaaa\0aaaaaaa\U{0004}aa\U{0002}a", "aaaaa\0aaaaaaa\U{0004}aa\U{0002}a\U{0006}\U{0008}");
expect |"aaaaa\0aaaaaaa\U{0004}aa\U{0002}a"| > |"aaaaa\0aaaaaaa\U{0004}aa\U{0002}a\U{0006}\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaa\0aaaaaaa\U{0004}aa\U{0002}a", "aaaaa\0aaaaaaa\U{0004}aa\U{0002}a\U{0006}\U{0008}");
}
method {:test} Test113() {
var r0 := isPrefix("\0aaaa\U{0008}aa\U{0010}aaaaaaaaaa\U{0004}\U{0016}", "\U{0002}aaaa\U{0006}a\U{000E}\U{000C}aaaaa\U{0012}aaa\n\U{0014}\U{0018}");
expect |"\0aaaa\U{0008}aa\U{0010}aaaaaaaaaa\U{0004}\U{0016}"| > |"\U{0002}aaaa\U{0006}a\U{000E}\U{000C}aaaaa\U{0012}aaa\n\U{0014}\U{0018}"| ==> !r0;
expect r0 == isPrefixPredicate("\0aaaa\U{0008}aa\U{0010}aaaaaaaaaa\U{0004}\U{0016}", "\U{0002}aaaa\U{0006}a\U{000E}\U{000C}aaaaa\U{0012}aaa\n\U{0014}\U{0018}");
}
method {:test} Test114() {
var r0 := isPrefix("aaaaa\U{0006}aaaa\U{0012}aa\U{0014}\n\U{0010}aaaa\U{001A}", "aaaa\0aa\U{000E}aa\U{0004}\U{0002}\U{0008}aa\U{0016}aa\U{0018}\U{000C}");
expect |"aaaaa\U{0006}aaaa\U{0012}aa\U{0014}\n\U{0010}aaaa\U{001A}"| > |"aaaa\0aa\U{000E}aa\U{0004}\U{0002}\U{0008}aa\U{0016}aa\U{0018}\U{000C}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaa\U{0006}aaaa\U{0012}aa\U{0014}\n\U{0010}aaaa\U{001A}", "aaaa\0aa\U{000E}aa\U{0004}\U{0002}\U{0008}aa\U{0016}aa\U{0018}\U{000C}");
}
method {:test} Test115() {
var r0 := isSubstring("aaaaaaaaaaaaa\U{000C}\n\U{000E}aa\U{0012}aaaaaa\U{0016}", "\U{0018}aa\0a\U{0006}aaa\U{0004}aaaa\U{0002}aa\U{0014}aaaaaa\U{0010}\U{0008}");
expect r0 == isSubstringPredicate("aaaaaaaaaaaaa\U{000C}\n\U{000E}aa\U{0012}aaaaaa\U{0016}", "\U{0018}aa\0a\U{0006}aaa\U{0004}aaaa\U{0002}aa\U{0014}aaaaaa\U{0010}\U{0008}");
}
method {:test} Test116() {
var r0 := isSubstring("\U{000C}aaaaaaaa\U{0004}\0aaaa\U{0008}", "\U{000E}aaaaa\U{0002}aa\U{0006}a\U{000C}aaaaaaaa\U{0004}\0aaaa\U{0008}\n");
expect r0 == isSubstringPredicate("\U{000C}aaaaaaaa\U{0004}\0aaaa\U{0008}", "\U{000E}aaaaa\U{0002}aa\U{0006}a\U{000C}aaaaaaaa\U{0004}\0aaaa\U{0008}\n");
}
method {:test} Test117() {
var r0 := isSubstring("aaaaaaaaaaaaaaa\U{0008}aaa\U{0010}aaa\U{000C}a\U{0006}aaa\U{0004}", "\U{0012}aa\0a\U{0002}aaaaaaaaaaa\U{000E}aaaaaa\na");
expect r0 == isSubstringPredicate("aaaaaaaaaaaaaaa\U{0008}aaa\U{0010}aaa\U{000C}a\U{0006}aaa\U{0004}", "\U{0012}aa\0a\U{0002}aaaaaaaaaaa\U{000E}aaaaaa\na");
}
method {:test} Test118() {
var r0 := haveCommonKSubstring(27, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 27 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 27 ==> !r0;
expect haveCommonKSubstringPredicate(27, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test119() {
var r0 := haveCommonKSubstring(28, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 28 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test120() {
var r0 := haveCommonKSubstring(30, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 30 || |"\0aaaaaaaaaaaaaaaaaa"| < 30 ==> !r0;
expect haveCommonKSubstringPredicate(30, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test121() {
var r0 := haveCommonKSubstring(35, "\U{0006}aaaaaaaaaaaa\0", "\U{0008}aaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaa");
expect |"\U{0006}aaaaaaaaaaaa\0"| < 35 || |"\U{0008}aaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaa"| < 35 ==> !r0;
expect haveCommonKSubstringPredicate(35, "\U{0006}aaaaaaaaaaaa\0", "\U{0008}aaaaaaaaaaaaaaaaaaa\U{0002}\U{0004}aaaaa") == r0;
}
method {:test} Test122() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaa\na\U{000C}a\0a\U{0006}aa", "aaa\U{0002}\U{0004}\U{0008}a");
expect r0 <= |"aaaaaaaaaaaaaaa\na\U{000C}a\0a\U{0006}aa"| && r0 <= |"aaa\U{0002}\U{0004}\U{0008}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaaa\na\U{000C}a\0a\U{0006}aa", "aaa\U{0002}\U{0004}\U{0008}a", r0);
}
method {:test} Test123() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaa\na\U{000C}a\U{0006}a\0aa", "aaa\U{0002}a\U{0008}\U{0004}");
expect r0 <= |"aaaaaaaaaaaaaaa\na\U{000C}a\U{0006}a\0aa"| && r0 <= |"aaa\U{0002}a\U{0008}\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaaa\na\U{000C}a\U{0006}a\0aa", "aaa\U{0002}a\U{0008}\U{0004}", r0);
}
method {:test} Test124() {
var r0 := maxCommonSubstringLength("\0aaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa");
expect r0 <= |"\0aaaaaaaaaaaaaaa"| && r0 <= |"\U{0002}aaaaaaaaaaaaaaaaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\0aaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa", r0);
}
method {:test} Test125() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaa\U{0006}\0\naaaaa\U{0008}", "aaa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{000C}a");
expect r0 <= |"aaaaaaaaaaaaaaa\U{0006}\0\naaaaa\U{0008}"| && r0 <= |"aaa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{000C}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaaa\U{0006}\0\naaaaa\U{0008}", "aaa\U{0002}a\U{0004}aaaaaaaaaaaaa\U{000C}a", r0);
}

// REPEAT 9 - TIME: 73.0498373 s

method {:test} Test126() {
var r0 := isPrefix("aaaaa\0a\U{0004}aaaaaaaaaaaaaaa\U{0002}", "aaaaa\0a\U{0004}aaaaaaaaaaaaaaa\U{0002}\U{0008}\U{0006}");
expect |"aaaaa\0a\U{0004}aaaaaaaaaaaaaaa\U{0002}"| > |"aaaaa\0a\U{0004}aaaaaaaaaaaaaaa\U{0002}\U{0008}\U{0006}"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaa\0a\U{0004}aaaaaaaaaaaaaaa\U{0002}", "aaaaa\0a\U{0004}aaaaaaaaaaaaaaa\U{0002}\U{0008}\U{0006}");
}
method {:test} Test127() {
var r0 := isPrefix("\0aaaaaa\U{0006}aaaaaaaa\U{0008}\naaaa", "\U{0002}aaaaaaaaaa\U{0004}aaaaa\U{000C}a\U{000E}aa");
expect |"\0aaaaaa\U{0006}aaaaaaaa\U{0008}\naaaa"| > |"\U{0002}aaaaaaaaaa\U{0004}aaaaa\U{000C}a\U{000E}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\0aaaaaa\U{0006}aaaaaaaa\U{0008}\naaaa", "\U{0002}aaaaaaaaaa\U{0004}aaaaa\U{000C}a\U{000E}aa");
}
method {:test} Test128() {
var r0 := isPrefix("aaaaaaa\U{0006}aaaaaaaaa\naaaaa", "aaa\U{0002}aaaaaaa\U{0004}aaa\U{0008}a\0aaaa");
expect |"aaaaaaa\U{0006}aaaaaaaaa\naaaaa"| > |"aaa\U{0002}aaaaaaa\U{0004}aaa\U{0008}a\0aaaa"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaa\U{0006}aaaaaaaaa\naaaaa", "aaa\U{0002}aaaaaaa\U{0004}aaa\U{0008}a\0aaaa");
}
method {:test} Test129() {
var r0 := isSubstring("aaaaa\0a\U{0002}aaaaaaaaaaaaaaaaa", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}");
expect r0 == isSubstringPredicate("aaaaa\0a\U{0002}aaaaaaaaaaaaaaaaa", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaaa\U{0006}\U{0004}");
}
method {:test} Test130() {
var r0 := isSubstring("\U{0006}aaaaaaa\U{0004}aaaaaa", "\U{0008}aaaa\0\U{0002}aaa\U{0006}aaaaaaa\U{0004}aaaaaa");
expect r0 == isSubstringPredicate("\U{0006}aaaaaaa\U{0004}aaaaaa", "\U{0008}aaaa\0\U{0002}aaa\U{0006}aaaaaaa\U{0004}aaaaaa");
}
method {:test} Test131() {
var r0 := isSubstring("aaaaaaaaaaa\U{0004}\U{0006}aa\U{0008}aaa", "\naaaa\0aaaaaaa\U{0002}a");
expect r0 == isSubstringPredicate("aaaaaaaaaaa\U{0004}\U{0006}aa\U{0008}aaa", "\naaaa\0aaaaaaa\U{0002}a");
}
method {:test} Test132() {
var r0 := haveCommonKSubstring(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test133() {
var r0 := haveCommonKSubstring(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 || |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test134() {
var r0 := haveCommonKSubstring(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test135() {
var r0 := haveCommonKSubstring(36, "\U{0004}aaaaaaaaaaaa\0aaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaa");
expect |"\U{0004}aaaaaaaaaaaa\0aaaaaaaa"| < 36 || |"\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaa"| < 36 ==> !r0;
expect haveCommonKSubstringPredicate(36, "\U{0004}aaaaaaaaaaaa\0aaaaaaaa", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaa") == r0;
}
method {:test} Test136() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaa\U{0008}a\n\U{0002}aaaaaa", "aaa\U{0006}\0\U{0004}aa");
expect r0 <= |"aaaaaaaaaaaaaaa\U{0008}a\n\U{0002}aaaaaa"| && r0 <= |"aaa\U{0006}\0\U{0004}aa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaaa\U{0008}a\n\U{0002}aaaaaa", "aaa\U{0006}\0\U{0004}aa", r0);
}
method {:test} Test138() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaaaa\U{000E}aaaaa\n\U{000C}", "aaaaaaa\0a\U{0008}a\U{0006}aa\U{0004}aaaa\U{0002}aa");
expect r0 <= |"aaaaaaaaaaaaaaaaa\U{000E}aaaaa\n\U{000C}"| && r0 <= |"aaaaaaa\0a\U{0008}a\U{0006}aa\U{0004}aaaa\U{0002}aa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaaaaa\U{000E}aaaaa\n\U{000C}", "aaaaaaa\0a\U{0008}a\U{0006}aa\U{0004}aaaa\U{0002}aa", r0);
}
method {:test} Test139() {
var r0 := maxCommonSubstringLength("\U{0008}aaaa\U{0004}aaaaaaaaaaaaaaaaaaa", "\U{0006}a\U{0002}\0");
expect r0 <= |"\U{0008}aaaa\U{0004}aaaaaaaaaaaaaaaaaaa"| && r0 <= |"\U{0006}a\U{0002}\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0008}aaaa\U{0004}aaaaaaaaaaaaaaaaaaa", "\U{0006}a\U{0002}\0", r0);
}

// REPEAT 10 - TIME: 85.003962 s

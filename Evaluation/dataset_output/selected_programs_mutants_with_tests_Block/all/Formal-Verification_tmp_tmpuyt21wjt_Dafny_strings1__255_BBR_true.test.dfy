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
  if true {
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

// REPEAT 1 - TIME: 9.2083269 s

method {:test} Test14() {
var r0 := isPrefix("aaa", "aaa");
expect |"aaa"| > |"aaa"| ==> !r0;
expect r0 == isPrefixPredicate("aaa", "aaa");
}
method {:test} Test15() {
var r0 := isPrefix("\U{0006}\0\U{0004}", "\U{0006}\U{0002}\U{0004}");
expect |"\U{0006}\0\U{0004}"| > |"\U{0006}\U{0002}\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\0\U{0004}", "\U{0006}\U{0002}\U{0004}");
}
method {:test} Test16() {
var r0 := isPrefix("\U{0006}\U{0002}\U{0004}", "\U{0008}\0");
expect |"\U{0006}\U{0002}\U{0004}"| > |"\U{0008}\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\U{0002}\U{0004}", "\U{0008}\0");
}
method {:test} Test17() {
var r0 := isSubstring("aa\U{0002}", "\U{0004}\0a");
expect r0 == isSubstringPredicate("aa\U{0002}", "\U{0004}\0a");
}
method {:test} Test18() {
var r0 := isSubstring("", "\U{0002}\0");
expect r0 == isSubstringPredicate("", "\U{0002}\0");
}
method {:test} Test19() {
var r0 := isSubstring("\U{0002}aaaaaaaaa\0aa", "aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0002}aaaaaaaaa\0aa", "aaaaaaaaaaaa");
}
method {:test} Test20() {
var r0 := haveCommonKSubstring(3, "\U{0006}\0\U{0004}", "a\U{0002}a");
expect |"\U{0006}\0\U{0004}"| < 3 || |"a\U{0002}a"| < 3 ==> !r0;
expect haveCommonKSubstringPredicate(3, "\U{0006}\0\U{0004}", "a\U{0002}a") == r0;
}
method {:test} Test21() {
var r0 := haveCommonKSubstring(5, "aaaaaaaaaaaa", "aaaaaaaa");
expect |"aaaaaaaaaaaa"| < 5 || |"aaaaaaaa"| < 5 ==> !r0;
expect haveCommonKSubstringPredicate(5, "aaaaaaaaaaaa", "aaaaaaaa") == r0;
}
method {:test} Test22() {
var r0 := haveCommonKSubstring(3, "\U{0004}\U{0002}", "\U{0006}\0");
expect |"\U{0004}\U{0002}"| < 3 || |"\U{0006}\0"| < 3 ==> !r0;
expect haveCommonKSubstringPredicate(3, "\U{0004}\U{0002}", "\U{0006}\0") == r0;
}
method {:test} Test23() {
var r0 := maxCommonSubstringLength("aaa", "a\0");
expect r0 <= |"aaa"| && r0 <= |"a\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaa", "a\0", r0);
}
method {:test} Test25() {
var r0 := maxCommonSubstringLength("a\U{0002}a\U{0006}", "a\0aaaaaaaaaaaaaaaaa\U{0004}");
expect r0 <= |"a\U{0002}a\U{0006}"| && r0 <= |"a\0aaaaaaaaaaaaaaaaa\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\U{0002}a\U{0006}", "a\0aaaaaaaaaaaaaaaaa\U{0004}", r0);
}
method {:test} Test26() {
var r0 := maxCommonSubstringLength("aa\0", "a\U{0002}");
expect r0 <= |"aa\0"| && r0 <= |"a\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aa\0", "a\U{0002}", r0);
}

// REPEAT 2 - TIME: 14.4958209 s

method {:test} Test27() {
var r0 := isPrefix("\U{0002}\0aa", "\U{0002}\0aa");
expect |"\U{0002}\0aa"| > |"\U{0002}\0aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0aa", "\U{0002}\0aa");
}
method {:test} Test28() {
var r0 := isPrefix("\0aa\U{0004}", "\U{0002}aaa");
expect |"\0aa\U{0004}"| > |"\U{0002}aaa"| ==> !r0;
expect r0 == isPrefixPredicate("\0aa\U{0004}", "\U{0002}aaa");
}
method {:test} Test29() {
var r0 := isPrefix("\U{0004}a\U{0002}\U{0006}aaaaaa\U{0008}", "a\0aaaaaaa\n");
expect |"\U{0004}a\U{0002}\U{0006}aaaaaa\U{0008}"| > |"a\0aaaaaaa\n"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}a\U{0002}\U{0006}aaaaaa\U{0008}", "a\0aaaaaaa\n");
}
method {:test} Test30() {
var r0 := isSubstring("\U{0002}\0aa", "\U{0004}aaa");
expect r0 == isSubstringPredicate("\U{0002}\0aa", "\U{0004}aaa");
}
method {:test} Test31() {
var r0 := isSubstring("\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaa", "\U{0004}\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaa", "\U{0004}\U{0006}aaaa\U{0002}aaaaaaaaaa\0aaaaaaaaaaaa");
}
method {:test} Test32() {
var r0 := isSubstring("\0aa\U{0004}", "\U{0002}a");
expect r0 == isSubstringPredicate("\0aa\U{0004}", "\U{0002}a");
}
method {:test} Test33() {
var r0 := haveCommonKSubstring(6, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}", "aaa\U{0002}aaa\U{0006}a");
expect |"\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}"| < 6 || |"aaa\U{0002}aaa\U{0006}a"| < 6 ==> !r0;
expect haveCommonKSubstringPredicate(6, "\U{0004}\0aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}", "aaa\U{0002}aaa\U{0006}a") == r0;
}
method {:test} Test34() {
var r0 := haveCommonKSubstring(7, "aaaaaaaaaaaa\U{0002}aaaaaaa", "aaaaaaaa\0aaaaaaaaaaa");
expect |"aaaaaaaaaaaa\U{0002}aaaaaaa"| < 7 || |"aaaaaaaa\0aaaaaaaaaaa"| < 7 ==> !r0;
expect haveCommonKSubstringPredicate(7, "aaaaaaaaaaaa\U{0002}aaaaaaa", "aaaaaaaa\0aaaaaaaaaaa") == r0;
}
method {:test} Test35() {
var r0 := haveCommonKSubstring(10, "\U{0004}aaaaaaaaa", "a\U{0002}a\U{0006}aaaa\0");
expect |"\U{0004}aaaaaaaaa"| < 10 || |"a\U{0002}a\U{0006}aaaa\0"| < 10 ==> !r0;
expect haveCommonKSubstringPredicate(10, "\U{0004}aaaaaaaaa", "a\U{0002}a\U{0006}aaaa\0") == r0;
}
method {:test} Test36() {
var r0 := haveCommonKSubstring(6, "\U{0008}a\U{0002}", "\U{0004}\0a\U{0006}");
expect |"\U{0008}a\U{0002}"| < 6 || |"\U{0004}\0a\U{0006}"| < 6 ==> !r0;
expect haveCommonKSubstringPredicate(6, "\U{0008}a\U{0002}", "\U{0004}\0a\U{0006}") == r0;
}
method {:test} Test37() {
var r0 := maxCommonSubstringLength("\U{0002}aaa", "\U{0004}\0a");
expect r0 <= |"\U{0002}aaa"| && r0 <= |"\U{0004}\0a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}aaa", "\U{0004}\0a", r0);
}
method {:test} Test39() {
var r0 := maxCommonSubstringLength("\U{0006}\0", "\U{0004}aaaaaaaaaaaaaaaaa\U{0002}aaaaaa");
expect r0 <= |"\U{0006}\0"| && r0 <= |"\U{0004}aaaaaaaaaaaaaaaaa\U{0002}aaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}\0", "\U{0004}aaaaaaaaaaaaaaaaa\U{0002}aaaaaa", r0);
}
method {:test} Test40() {
var r0 := maxCommonSubstringLength("\U{0008}\0a", "\U{0004}a\U{0002}\U{0006}");
expect r0 <= |"\U{0008}\0a"| && r0 <= |"\U{0004}a\U{0002}\U{0006}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0008}\0a", "\U{0004}a\U{0002}\U{0006}", r0);
}

// REPEAT 3 - TIME: 20.3894023 s

method {:test} Test41() {
var r0 := isPrefix("\U{0002}aa\0a", "\U{0002}aa\0aa");
expect |"\U{0002}aa\0a"| > |"\U{0002}aa\0aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}aa\0a", "\U{0002}aa\0aa");
}
method {:test} Test42() {
var r0 := isPrefix("\U{0008}\0aaaaaaaaaaa\U{0006}\U{0004}", "\naaaaaaaaaaa\U{0002}aa");
expect |"\U{0008}\0aaaaaaaaaaa\U{0006}\U{0004}"| > |"\naaaaaaaaaaa\U{0002}aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}\0aaaaaaaaaaa\U{0006}\U{0004}", "\naaaaaaaaaaa\U{0002}aa");
}
method {:test} Test43() {
var r0 := isPrefix("\U{0004}\0aaaaa\na\U{000C}\U{0010}\U{0006}", "\U{0002}aa\U{0008}aaaaa\U{000E}a");
expect |"\U{0004}\0aaaaa\na\U{000C}\U{0010}\U{0006}"| > |"\U{0002}aa\U{0008}aaaaa\U{000E}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\0aaaaa\na\U{000C}\U{0010}\U{0006}", "\U{0002}aa\U{0008}aaaaa\U{000E}a");
}
method {:test} Test44() {
var r0 := isSubstring("\U{0002}\0", "\U{0004}aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0002}\0", "\U{0004}aaaaaaaaaaaa");
}
method {:test} Test45() {
var r0 := isSubstring("\U{000C}\0aaaaaaaa\U{0006}\U{0008}a\U{0004}aaaaa", "\naaa\U{0002}\U{000C}\0aaaaaaaa\U{0006}\U{0008}a\U{0004}aaaaa");
expect r0 == isSubstringPredicate("\U{000C}\0aaaaaaaa\U{0006}\U{0008}a\U{0004}aaaaa", "\naaa\U{0002}\U{000C}\0aaaaaaaa\U{0006}\U{0008}a\U{0004}aaaaa");
}
method {:test} Test46() {
var r0 := isSubstring("\U{0004}aaaaa\U{000C}aaa\U{000E}\U{0002}\n", "\U{0010}\0a\U{0008}aaaaa\U{0006}aa");
expect r0 == isSubstringPredicate("\U{0004}aaaaa\U{000C}aaa\U{000E}\U{0002}\n", "\U{0010}\0a\U{0008}aaaaa\U{0006}aa");
}
method {:test} Test47() {
var r0 := haveCommonKSubstring(11, "aaaaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{0006}", "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaa\U{0004}");
expect |"aaaaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{0006}"| < 11 || |"aaaaaaaaaaa\0aaaaaaaaaaaaaaaaa\U{0004}"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "aaaaaaaaaaaaaaaaa\U{0002}aaaaaaa\U{0006}", "aaaaaaaaaaa\0aaaaaaaaaaaaaaaaa\U{0004}") == r0;
}
method {:test} Test48() {
var r0 := haveCommonKSubstring(13, "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}"| < 13 || |"aaaaaaaaaaaaaaaaaaaaaaaaa\0"| < 13 ==> !r0;
expect haveCommonKSubstringPredicate(13, "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}", "aaaaaaaaaaaaaaaaaaaaaaaaa\0") == r0;
}
method {:test} Test49() {
var r0 := haveCommonKSubstring(11, "\U{0012}aa\U{000C}\U{0004}\U{0002}aa\n\U{0006}a", "\U{0010}\0a\U{0008}\U{000E}");
expect |"\U{0012}aa\U{000C}\U{0004}\U{0002}aa\n\U{0006}a"| < 11 || |"\U{0010}\0a\U{0008}\U{000E}"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "\U{0012}aa\U{000C}\U{0004}\U{0002}aa\n\U{0006}a", "\U{0010}\0a\U{0008}\U{000E}") == r0;
}
method {:test} Test50() {
var r0 := haveCommonKSubstring(11, "\U{0010}\0a\U{0006}", "\naaaa\U{0008}a\U{0002}a\U{000E}aaaa\U{000C}aaaa\U{0004}aaaaaa");
expect |"\U{0010}\0a\U{0006}"| < 11 || |"\naaaa\U{0008}a\U{0002}a\U{000E}aaaa\U{000C}aaaa\U{0004}aaaaaa"| < 11 ==> !r0;
expect haveCommonKSubstringPredicate(11, "\U{0010}\0a\U{0006}", "\naaaa\U{0008}a\U{0002}a\U{000E}aaaa\U{000C}aaaa\U{0004}aaaaaa") == r0;
}
method {:test} Test51() {
var r0 := maxCommonSubstringLength("a\U{0002}\U{0008}\U{000C}\n", "\U{0004}aaaaaaaaaaa\U{000E}aa\U{0006}aaa\0aaaaa\U{0010}");
expect r0 <= |"a\U{0002}\U{0008}\U{000C}\n"| && r0 <= |"\U{0004}aaaaaaaaaaa\U{000E}aa\U{0006}aaa\0aaaaa\U{0010}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\U{0002}\U{0008}\U{000C}\n", "\U{0004}aaaaaaaaaaa\U{000E}aa\U{0006}aaa\0aaaaa\U{0010}", r0);
}
method {:test} Test53() {
var r0 := maxCommonSubstringLength("\0", "\U{0002}");
expect r0 <= |"\0"| && r0 <= |"\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\0", "\U{0002}", r0);
}
method {:test} Test54() {
var r0 := maxCommonSubstringLength("\U{0002}aaaaaaaaaaaaaaaaaaa", "\0a");
expect r0 <= |"\U{0002}aaaaaaaaaaaaaaaaaaa"| && r0 <= |"\0a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}aaaaaaaaaaaaaaaaaaa", "\0a", r0);
}

// REPEAT 4 - TIME: 26.9411087 s

method {:test} Test55() {
var r0 := isPrefix("\U{0004}\U{0002}aa", "\U{0004}\U{0002}aa\U{0006}aaaa\0aaaaaaaa");
expect |"\U{0004}\U{0002}aa"| > |"\U{0004}\U{0002}aa\U{0006}aaaa\0aaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0004}\U{0002}aa", "\U{0004}\U{0002}aa\U{0006}aaaa\0aaaaaaaa");
}
method {:test} Test56() {
var r0 := isPrefix("\U{0002}aa\U{0006}a\U{000C}aa\n\U{000E}", "\U{0012}\0aa\U{0008}aa\U{0004}a\U{0010}");
expect |"\U{0002}aa\U{0006}a\U{000C}aa\n\U{000E}"| > |"\U{0012}\0aa\U{0008}aa\U{0004}a\U{0010}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}aa\U{0006}a\U{000C}aa\n\U{000E}", "\U{0012}\0aa\U{0008}aa\U{0004}a\U{0010}");
}
method {:test} Test57() {
var r0 := isPrefix("\naa\U{0004}a\U{0006}", "\U{0008}\0\U{0002}a");
expect |"\naa\U{0004}a\U{0006}"| > |"\U{0008}\0\U{0002}a"| ==> !r0;
expect r0 == isPrefixPredicate("\naa\U{0004}a\U{0006}", "\U{0008}\0\U{0002}a");
}
method {:test} Test58() {
var r0 := isSubstring("\U{0006}\U{0002}a", "\U{0004}\0aaa");
expect r0 == isSubstringPredicate("\U{0006}\U{0002}a", "\U{0004}\0aaa");
}
method {:test} Test59() {
var r0 := isSubstring("\U{0004}\U{0002}", "\U{0006}\0aaaaa\U{0004}\U{0002}");
expect r0 == isSubstringPredicate("\U{0004}\U{0002}", "\U{0006}\0aaaaa\U{0004}\U{0002}");
}
method {:test} Test60() {
var r0 := isSubstring("\U{000C}\0aa\U{0004}aaaaaaa\U{0008}aa", "\naa\U{0002}aaaaa\U{0006}aaaa");
expect r0 == isSubstringPredicate("\U{000C}\0aa\U{0004}aaaaaaa\U{0008}aa", "\naa\U{0002}aaaaa\U{0006}aaaa");
}
method {:test} Test61() {
var r0 := haveCommonKSubstring(14, "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| < 14 || |"aaaaaaaaaaaaaaaaaaaaa"| < 14 ==> !r0;
expect haveCommonKSubstringPredicate(14, "aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "aaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test62() {
var r0 := haveCommonKSubstring(16, "aaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaa"| < 16 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaa"| < 16 ==> !r0;
expect haveCommonKSubstringPredicate(16, "aaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test63() {
var r0 := haveCommonKSubstring(14, "\U{000C}aa\U{0002}aaaaaaaa\U{0008}a", "\n\0a\U{0004}a\U{0006}");
expect |"\U{000C}aa\U{0002}aaaaaaaa\U{0008}a"| < 14 || |"\n\0a\U{0004}a\U{0006}"| < 14 ==> !r0;
expect haveCommonKSubstringPredicate(14, "\U{000C}aa\U{0002}aaaaaaaa\U{0008}a", "\n\0a\U{0004}a\U{0006}") == r0;
}
method {:test} Test64() {
var r0 := haveCommonKSubstring(14, "\U{001A}aa\U{0004}\U{0008}a\U{000C}", "\U{001C}\U{0002}\U{0006}aa\U{0010}a\U{0012}\0\U{0016}aa\U{0014}aaa\naaaaaaaa\U{000E}\U{0018}");
expect |"\U{001A}aa\U{0004}\U{0008}a\U{000C}"| < 14 || |"\U{001C}\U{0002}\U{0006}aa\U{0010}a\U{0012}\0\U{0016}aa\U{0014}aaa\naaaaaaaa\U{000E}\U{0018}"| < 14 ==> !r0;
expect haveCommonKSubstringPredicate(14, "\U{001A}aa\U{0004}\U{0008}a\U{000C}", "\U{001C}\U{0002}\U{0006}aa\U{0010}a\U{0012}\0\U{0016}aa\U{0014}aaa\naaaaaaaa\U{000E}\U{0018}") == r0;
}
method {:test} Test65() {
var r0 := maxCommonSubstringLength("\U{0006}\U{0002}a\U{0008}a\n", "\U{0004}\0");
expect r0 <= |"\U{0006}\U{0002}a\U{0008}a\n"| && r0 <= |"\U{0004}\0"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}\U{0002}a\U{0008}a\n", "\U{0004}\0", r0);
}
method {:test} Test67() {
var r0 := maxCommonSubstringLength("\U{0004}\0", "\U{0002}");
expect r0 <= |"\U{0004}\0"| && r0 <= |"\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}\0", "\U{0002}", r0);
}
method {:test} Test68() {
var r0 := maxCommonSubstringLength("a\U{0002}aaaaaaaa\U{0006}aaaaaa\U{000C}\na\U{0010}aaaaa", "\U{0004}aa\U{0008}a\0aaaaaaaaaaaaaaa\U{000E}");
expect r0 <= |"a\U{0002}aaaaaaaa\U{0006}aaaaaa\U{000C}\na\U{0010}aaaaa"| && r0 <= |"\U{0004}aa\U{0008}a\0aaaaaaaaaaaaaaa\U{000E}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\U{0002}aaaaaaaa\U{0006}aaaaaa\U{000C}\na\U{0010}aaaaa", "\U{0004}aa\U{0008}a\0aaaaaaaaaaaaaaa\U{000E}", r0);
}

// REPEAT 5 - TIME: 34.0606691 s

method {:test} Test69() {
var r0 := isPrefix("\U{0002}\0a\U{0006}a", "\U{0002}\0a\U{0006}a\U{0004}");
expect |"\U{0002}\0a\U{0006}a"| > |"\U{0002}\0a\U{0006}a\U{0004}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0002}\0a\U{0006}a", "\U{0002}\0a\U{0006}a\U{0004}");
}
method {:test} Test70() {
var r0 := isPrefix("\U{0006}\0aa\U{0002}", "\U{0008}aa\U{0004}a");
expect |"\U{0006}\0aa\U{0002}"| > |"\U{0008}aa\U{0004}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}\0aa\U{0002}", "\U{0008}aa\U{0004}a");
}
method {:test} Test71() {
var r0 := isPrefix("\U{000C}\0aa\U{0002}aa\U{0004}a\n", "\U{000E}aa\U{0006}\U{0008}");
expect |"\U{000C}\0aa\U{0002}aa\U{0004}a\n"| > |"\U{000E}aa\U{0006}\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}\0aa\U{0002}aa\U{0004}a\n", "\U{000E}aa\U{0006}\U{0008}");
}
method {:test} Test72() {
var r0 := isSubstring("\n\0a\U{0004}aaaaaaa\U{0002}aa", "\U{0008}aaaaaaaa\U{0006}aaaa");
expect r0 == isSubstringPredicate("\n\0a\U{0004}aaaaaaa\U{0002}aa", "\U{0008}aaaaaaaa\U{0006}aaaa");
}
method {:test} Test73() {
var r0 := isSubstring("\U{0004}\U{0002}", "\U{0006}a\0\U{0004}\U{0002}aa\U{0008}");
expect r0 == isSubstringPredicate("\U{0004}\U{0002}", "\U{0006}a\0\U{0004}\U{0002}aa\U{0008}");
}
method {:test} Test74() {
var r0 := isSubstring("\n\U{0004}a\U{0006}aaaaa\0aaaaaa", "\U{0008}aaaaaa\U{0002}aa");
expect r0 == isSubstringPredicate("\n\U{0004}a\U{0006}aaaaa\0aaaaaa", "\U{0008}aaaaaa\U{0002}aa");
}
method {:test} Test75() {
var r0 := haveCommonKSubstring(17, "aaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa\0a");
expect |"aaaaaaaaaaaaaaaaa"| < 17 || |"aaaaaaaaaaaaaaaaaaaaaaaaaa\0a"| < 17 ==> !r0;
expect haveCommonKSubstringPredicate(17, "aaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaa\0a") == r0;
}
method {:test} Test76() {
var r0 := haveCommonKSubstring(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 22 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 22 ==> !r0;
expect haveCommonKSubstringPredicate(22, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test77() {
var r0 := haveCommonKSubstring(17, "\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\U{0002}\0");
expect |"\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 17 || |"\U{0008}\U{0002}\0"| < 17 ==> !r0;
expect haveCommonKSubstringPredicate(17, "\U{0006}a\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0008}\U{0002}\0") == r0;
}
method {:test} Test78() {
var r0 := haveCommonKSubstring(17, "\U{0012}aa\U{0004}aaa\U{0008}aa\U{000C}a\U{0006}a\U{000E}", "\U{0010}aaaaaaaaaaaaaa\0\naaaa\U{0002}");
expect |"\U{0012}aa\U{0004}aaa\U{0008}aa\U{000C}a\U{0006}a\U{000E}"| < 17 || |"\U{0010}aaaaaaaaaaaaaa\0\naaaa\U{0002}"| < 17 ==> !r0;
expect haveCommonKSubstringPredicate(17, "\U{0012}aa\U{0004}aaa\U{0008}aa\U{000C}a\U{0006}a\U{000E}", "\U{0010}aaaaaaaaaaaaaa\0\naaaa\U{0002}") == r0;
}
method {:test} Test79() {
var r0 := maxCommonSubstringLength("a\0a\U{0002}a\U{0004}aaaaa\U{0008}aaaaaaaaaaaa\n", "\U{000C}aaa\U{0006}");
expect r0 <= |"a\0a\U{0002}a\U{0004}aaaaa\U{0008}aaaaaaaaaaaa\n"| && r0 <= |"\U{000C}aaa\U{0006}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0a\U{0002}a\U{0004}aaaaa\U{0008}aaaaaaaaaaaa\n", "\U{000C}aaa\U{0006}", r0);
}
method {:test} Test80() {
var r0 := maxCommonSubstringLength("a\0a\U{0004}a\naaaaaaaaa\U{0002}aaaaaa\U{0006}\U{000C}", "\U{000E}aaa\U{0008}");
expect r0 <= |"a\0a\U{0004}a\naaaaaaaaa\U{0002}aaaaaa\U{0006}\U{000C}"| && r0 <= |"\U{000E}aaa\U{0008}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0a\U{0004}a\naaaaaaaaa\U{0002}aaaaaa\U{0006}\U{000C}", "\U{000E}aaa\U{0008}", r0);
}
method {:test} Test81() {
var r0 := maxCommonSubstringLength("", "\U{0004}\na\U{0006}\U{0008}aaaaaaaaaaaa\0\U{0002}");
expect r0 <= |""| && r0 <= |"\U{0004}\na\U{0006}\U{0008}aaaaaaaaaaaa\0\U{0002}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("", "\U{0004}\na\U{0006}\U{0008}aaaaaaaaaaaa\0\U{0002}", r0);
}
method {:test} Test82() {
var r0 := maxCommonSubstringLength("\0\U{0002}", "\U{0006}a\U{0004}");
expect r0 <= |"\0\U{0002}"| && r0 <= |"\U{0006}a\U{0004}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\0\U{0002}", "\U{0006}a\U{0004}", r0);
}

// REPEAT 6 - TIME: 42.2977955 s

method {:test} Test83() {
var r0 := isPrefix("aa\U{0008}\U{000E}\U{0004}\U{0002}\na\0a\U{0006}\U{000C}a", "aa\U{0008}\U{000E}\U{0004}\U{0002}\na\0a\U{0006}\U{000C}a\U{0010}");
expect |"aa\U{0008}\U{000E}\U{0004}\U{0002}\na\0a\U{0006}\U{000C}a"| > |"aa\U{0008}\U{000E}\U{0004}\U{0002}\na\0a\U{0006}\U{000C}a\U{0010}"| ==> !r0;
expect r0 == isPrefixPredicate("aa\U{0008}\U{000E}\U{0004}\U{0002}\na\0a\U{0006}\U{000C}a", "aa\U{0008}\U{000E}\U{0004}\U{0002}\na\0a\U{0006}\U{000C}a\U{0010}");
}
method {:test} Test84() {
var r0 := isPrefix("\naaa\U{0004}", "\U{0008}\0a\U{0002}\U{0006}");
expect |"\naaa\U{0004}"| > |"\U{0008}\0a\U{0002}\U{0006}"| ==> !r0;
expect r0 == isPrefixPredicate("\naaa\U{0004}", "\U{0008}\0a\U{0002}\U{0006}");
}
method {:test} Test85() {
var r0 := isPrefix("\U{0014}aaaaaa\U{0008}a\U{0010}aaaa\U{000E}\n", "\U{0012}\0\U{0004}\U{0006}\U{0002}\U{000C}a");
expect |"\U{0014}aaaaaa\U{0008}a\U{0010}aaaa\U{000E}\n"| > |"\U{0012}\0\U{0004}\U{0006}\U{0002}\U{000C}a"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0014}aaaaaa\U{0008}a\U{0010}aaaa\U{000E}\n", "\U{0012}\0\U{0004}\U{0006}\U{0002}\U{000C}a");
}
method {:test} Test86() {
var r0 := isSubstring("\U{000E}aa\U{0004}a\U{0008}aaaa\naa\U{0002}a", "\U{000C}aa\0aaaaaaaaaaa\U{0006}aaaaa");
expect r0 == isSubstringPredicate("\U{000E}aa\U{0004}a\U{0008}aaaa\naa\U{0002}a", "\U{000C}aa\0aaaaaaaaaaa\U{0006}aaaaa");
}
method {:test} Test87() {
var r0 := isSubstring("\U{0006}aaaaa\U{0008}aaa\U{0002}aaaa", "\U{0004}aaa\0a\U{0006}aaaaa\U{0008}aaa\U{0002}aaaaaa");
expect r0 == isSubstringPredicate("\U{0006}aaaaa\U{0008}aaa\U{0002}aaaa", "\U{0004}aaa\0a\U{0006}aaaaa\U{0008}aaa\U{0002}aaaaaa");
}
method {:test} Test88() {
var r0 := isSubstring("\naaa\U{0004}aaaa\U{0002}aaaa", "\U{0008}aa\0aaa\U{0006}");
expect r0 == isSubstringPredicate("\naaa\U{0004}aaaa\U{0002}aaaa", "\U{0008}aa\0aaa\U{0006}");
}
method {:test} Test89() {
var r0 := haveCommonKSubstring(23, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaa"| < 23 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 23 ==> !r0;
expect haveCommonKSubstringPredicate(23, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test90() {
var r0 := haveCommonKSubstring(24, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"aaaaaaaaaaaaaaaaaaaaaaaaa"| < 24 || |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 24 ==> !r0;
expect haveCommonKSubstringPredicate(24, "aaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test91() {
var r0 := haveCommonKSubstring(27, "\naaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0008}aaaa\0aaaaaaaaaaaaaaa\U{0006}aaa\U{0002}");
expect |"\naaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a"| < 27 || |"\U{0008}aaaa\0aaaaaaaaaaaaaaa\U{0006}aaa\U{0002}"| < 27 ==> !r0;
expect haveCommonKSubstringPredicate(27, "\naaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}a", "\U{0008}aaaa\0aaaaaaaaaaaaaaa\U{0006}aaa\U{0002}") == r0;
}
method {:test} Test92() {
var r0 := haveCommonKSubstring(23, "\U{000E}aaaaaa\U{0004}aaaaaaa\U{0006}aaaaa\U{0008}", "\U{000C}aaaa\0aaaa\U{0002}aaaaaaaaaaa\n");
expect |"\U{000E}aaaaaa\U{0004}aaaaaaa\U{0006}aaaaa\U{0008}"| < 23 || |"\U{000C}aaaa\0aaaa\U{0002}aaaaaaaaaaa\n"| < 23 ==> !r0;
expect haveCommonKSubstringPredicate(23, "\U{000E}aaaaaa\U{0004}aaaaaaa\U{0006}aaaaa\U{0008}", "\U{000C}aaaa\0aaaa\U{0002}aaaaaaaaaaa\n") == r0;
}
method {:test} Test93() {
var r0 := maxCommonSubstringLength("\U{0004}\0aaaaaaaaaa\U{0008}aa\U{0002}\U{000C}aaa\na\U{000E}aaa\U{0014}", "aaa\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0010}\U{0012}a");
expect r0 <= |"\U{0004}\0aaaaaaaaaa\U{0008}aa\U{0002}\U{000C}aaa\na\U{000E}aaa\U{0014}"| && r0 <= |"aaa\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0010}\U{0012}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}\0aaaaaaaaaa\U{0008}aa\U{0002}\U{000C}aaa\na\U{000E}aaa\U{0014}", "aaa\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0010}\U{0012}a", r0);
}
method {:test} Test94() {
var r0 := maxCommonSubstringLength("\U{0004}\0aaa\naaaaaaaaa\U{0002}aaaa\U{000C}aaaa\U{0008}\U{0012}", "aaa\U{0006}aaaaaaaaaaaaaaaaaaaa\U{000E}\U{0010}a");
expect r0 <= |"\U{0004}\0aaa\naaaaaaaaa\U{0002}aaaa\U{000C}aaaa\U{0008}\U{0012}"| && r0 <= |"aaa\U{0006}aaaaaaaaaaaaaaaaaaaa\U{000E}\U{0010}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}\0aaa\naaaaaaaaa\U{0002}aaaa\U{000C}aaaa\U{0008}\U{0012}", "aaa\U{0006}aaaaaaaaaaaaaaaaaaaa\U{000E}\U{0010}a", r0);
}
method {:test} Test95() {
var r0 := maxCommonSubstringLength("a\0aaaaaaaaaaaaaaaaaa\naa\U{0008}\U{000C}a\U{000E}", "\U{0004}aa\U{0002}a\U{0006}");
expect r0 <= |"a\0aaaaaaaaaaaaaaaaaa\naa\U{0008}\U{000C}a\U{000E}"| && r0 <= |"\U{0004}aa\U{0002}a\U{0006}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0aaaaaaaaaaaaaaaaaa\naa\U{0008}\U{000C}a\U{000E}", "\U{0004}aa\U{0002}a\U{0006}", r0);
}
method {:test} Test96() {
var r0 := maxCommonSubstringLength("aaaa\U{0006}aaaa\U{0010}aaaaaaaaa\na\U{000C}a\U{0016}a\U{001A}\U{0012}a", "\U{0002}aa\U{0008}a\U{0014}a\0aaaaaaa\U{0004}\U{000E}aaaa\U{0018}\U{001C}aa\U{001E}a");
expect r0 <= |"aaaa\U{0006}aaaa\U{0010}aaaaaaaaa\na\U{000C}a\U{0016}a\U{001A}\U{0012}a"| && r0 <= |"\U{0002}aa\U{0008}a\U{0014}a\0aaaaaaa\U{0004}\U{000E}aaaa\U{0018}\U{001C}aa\U{001E}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaa\U{0006}aaaa\U{0010}aaaaaaaaa\na\U{000C}a\U{0016}a\U{001A}\U{0012}a", "\U{0002}aa\U{0008}a\U{0014}a\0aaaaaaa\U{0004}\U{000E}aaaa\U{0018}\U{001C}aa\U{001E}a", r0);
}

// REPEAT 7 - TIME: 50.7637434 s

method {:test} Test97() {
var r0 := isPrefix("aa\U{000C}\n\U{0006}\U{0010}a\U{0016}", "aa\U{000C}\n\U{0006}\U{0010}a\U{0016}aaa\0\U{0018}\U{0012}\U{000E}\U{001A}a\U{0008}\U{0002}\U{0004}\U{0014}aaaa\U{001C}");
expect |"aa\U{000C}\n\U{0006}\U{0010}a\U{0016}"| > |"aa\U{000C}\n\U{0006}\U{0010}a\U{0016}aaa\0\U{0018}\U{0012}\U{000E}\U{001A}a\U{0008}\U{0002}\U{0004}\U{0014}aaaa\U{001C}"| ==> !r0;
expect r0 == isPrefixPredicate("aa\U{000C}\n\U{0006}\U{0010}a\U{0016}", "aa\U{000C}\n\U{0006}\U{0010}a\U{0016}aaa\0\U{0018}\U{0012}\U{000E}\U{001A}a\U{0008}\U{0002}\U{0004}\U{0014}aaaa\U{001C}");
}
method {:test} Test98() {
var r0 := isPrefix("aa\U{0008}aaaa\naaa\U{0006}\U{000C}aa\U{0014}aa\U{0012}", "aa\U{0016}aaaaaaa\U{000E}\U{0004}aaaa\U{0010}aa\0\U{0002}");
expect |"aa\U{0008}aaaa\naaa\U{0006}\U{000C}aa\U{0014}aa\U{0012}"| > |"aa\U{0016}aaaaaaa\U{000E}\U{0004}aaaa\U{0010}aa\0\U{0002}"| ==> !r0;
expect r0 == isPrefixPredicate("aa\U{0008}aaaa\naaa\U{0006}\U{000C}aa\U{0014}aa\U{0012}", "aa\U{0016}aaaaaaa\U{000E}\U{0004}aaaa\U{0010}aa\0\U{0002}");
}
method {:test} Test99() {
var r0 := isPrefix("\U{0008}aaaa\U{0006}aaaaa\U{0004}aa", "\naaaaaaaaa\U{0002}\0");
expect |"\U{0008}aaaa\U{0006}aaaaa\U{0004}aa"| > |"\naaaaaaaaa\U{0002}\0"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0008}aaaa\U{0006}aaaaa\U{0004}aa", "\naaaaaaaaa\U{0002}\0");
}
method {:test} Test100() {
var r0 := isSubstring("\U{000C}aa\0aa\U{0004}aaaaaaaaa\U{0006}aaaa", "\naaaaaaa\U{0002}aa\U{0008}aaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{000C}aa\0aa\U{0004}aaaaaaaaa\U{0006}aaaa", "\naaaaaaa\U{0002}aa\U{0008}aaaaaaaaaaaaa");
}
method {:test} Test101() {
var r0 := isSubstring("\U{0008}aa\U{0006}aaaaaaaa\U{0004}aa", "\naaaaaaaa\0aaa\U{0002}\U{0008}aa\U{0006}aaaaaaaa\U{0004}aa");
expect r0 == isSubstringPredicate("\U{0008}aa\U{0006}aaaaaaaa\U{0004}aa", "\naaaaaaaa\0aaa\U{0002}\U{0008}aa\U{0006}aaaaaaaa\U{0004}aa");
}
method {:test} Test102() {
var r0 := isSubstring("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa\0aa");
expect r0 == isSubstringPredicate("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaa\0aa");
}
method {:test} Test103() {
var r0 := haveCommonKSubstring(28, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 28 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test104() {
var r0 := haveCommonKSubstring(28, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 28 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test105() {
var r0 := haveCommonKSubstring(30, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 30 || |"\0aaaaa"| < 30 ==> !r0;
expect haveCommonKSubstringPredicate(30, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaa") == r0;
}
method {:test} Test106() {
var r0 := haveCommonKSubstring(28, "\U{0004}aaaaaaaaaaaaaa\0", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa");
expect |"\U{0004}aaaaaaaaaaaaaa\0"| < 28 || |"\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa"| < 28 ==> !r0;
expect haveCommonKSubstringPredicate(28, "\U{0004}aaaaaaaaaaaaaa\0", "\U{0006}aaaaaaaaaaaaaaaaaaaa\U{0002}aaaaaaa") == r0;
}
method {:test} Test107() {
var r0 := maxCommonSubstringLength("a\0a\U{000C}\U{0010}aaaaaaaaaaaaaaaaa\U{0014}a\U{000E}a\U{0008}\U{001A}\U{0012}", "\U{0006}aaaaaaaaaaaa\naaaaaaaaa\U{0004}\U{0002}\U{0018}a\U{0016}");
expect r0 <= |"a\0a\U{000C}\U{0010}aaaaaaaaaaaaaaaaa\U{0014}a\U{000E}a\U{0008}\U{001A}\U{0012}"| && r0 <= |"\U{0006}aaaaaaaaaaaa\naaaaaaaaa\U{0004}\U{0002}\U{0018}a\U{0016}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0a\U{000C}\U{0010}aaaaaaaaaaaaaaaaa\U{0014}a\U{000E}a\U{0008}\U{001A}\U{0012}", "\U{0006}aaaaaaaaaaaa\naaaaaaaaa\U{0004}\U{0002}\U{0018}a\U{0016}", r0);
}
method {:test} Test109() {
var r0 := maxCommonSubstringLength("\U{0002}aaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 <= |"\U{0002}aaaaaaaaaaaaaaaaaaaa"| && r0 <= |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}aaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaa", r0);
}
method {:test} Test110() {
var r0 := maxCommonSubstringLength("\U{0002}aaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaa\n", "\U{0006}aa\U{0004}aaaaaaaaaaaaaa\0aaa\U{000C}");
expect r0 <= |"\U{0002}aaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaa\n"| && r0 <= |"\U{0006}aa\U{0004}aaaaaaaaaaaaaa\0aaa\U{000C}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}aaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaa\n", "\U{0006}aa\U{0004}aaaaaaaaaaaaaa\0aaa\U{000C}", r0);
}

// REPEAT 8 - TIME: 60.0697292 s

method {:test} Test111() {
var r0 := isPrefix("\U{000C}aaaaa\naaaaaaaaaa\U{0004}\U{0002}a", "\U{000C}aaaaa\naaaaaaaaaa\U{0004}\U{0002}aaaa\U{0006}a\U{0008}a\0aa");
expect |"\U{000C}aaaaa\naaaaaaaaaa\U{0004}\U{0002}a"| > |"\U{000C}aaaaa\naaaaaaaaaa\U{0004}\U{0002}aaaa\U{0006}a\U{0008}a\0aa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{000C}aaaaa\naaaaaaaaaa\U{0004}\U{0002}a", "\U{000C}aaaaa\naaaaaaaaaa\U{0004}\U{0002}aaaa\U{0006}a\U{0008}a\0aa");
}
method {:test} Test112() {
var r0 := isPrefix("a\U{001C}a\U{000E}a\naaa\U{0002}aaa\U{0006}\U{0016}\U{0012}a\U{0018}a\U{0014}", "a\U{001E}aa\U{0010}\U{0004}aaaaa\U{000C}aaa\U{0008}aa\0a\U{001A}a");
expect |"a\U{001C}a\U{000E}a\naaa\U{0002}aaa\U{0006}\U{0016}\U{0012}a\U{0018}a\U{0014}"| > |"a\U{001E}aa\U{0010}\U{0004}aaaaa\U{000C}aaa\U{0008}aa\0a\U{001A}a"| ==> !r0;
expect r0 == isPrefixPredicate("a\U{001C}a\U{000E}a\naaa\U{0002}aaa\U{0006}\U{0016}\U{0012}a\U{0018}a\U{0014}", "a\U{001E}aa\U{0010}\U{0004}aaaaa\U{000C}aaa\U{0008}aa\0a\U{001A}a");
}
method {:test} Test113() {
var r0 := isPrefix("a\0aaaa\U{0006}aaaa\U{0012}\U{000C}\U{000E}aaa\U{0014}\U{0010}\U{0004}", "aaa\na\U{0008}\U{0002}aaaaaaaaa");
expect |"a\0aaaa\U{0006}aaaa\U{0012}\U{000C}\U{000E}aaa\U{0014}\U{0010}\U{0004}"| > |"aaa\na\U{0008}\U{0002}aaaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("a\0aaaa\U{0006}aaaa\U{0012}\U{000C}\U{000E}aaa\U{0014}\U{0010}\U{0004}", "aaa\na\U{0008}\U{0002}aaaaaaaaa");
}
method {:test} Test114() {
var r0 := isSubstring("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aa\U{0002}aaaaaaa\0aaaaaaaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aa\U{0002}aaaaaaa\0aaaaaaaaaaaaaaaaaa");
}
method {:test} Test115() {
var r0 := isSubstring("\U{0004}aaaaaaaaaaaaaaaa", "\U{0002}aaa\0aaaaa\U{0004}aaaaaaaaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0004}aaaaaaaaaaaaaaaa", "\U{0002}aaa\0aaaaa\U{0004}aaaaaaaaaaaaaaaaaaa");
}
method {:test} Test116() {
var r0 := isSubstring("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test117() {
var r0 := haveCommonKSubstring(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test118() {
var r0 := haveCommonKSubstring(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| < 29 || |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaaa\0") == r0;
}
method {:test} Test119() {
var r0 := haveCommonKSubstring(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 29 || |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"| < 29 ==> !r0;
expect haveCommonKSubstringPredicate(29, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test120() {
var r0 := haveCommonKSubstring(31, "\U{0008}aaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0", "\naaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaa");
expect |"\U{0008}aaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0"| < 31 || |"\naaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaa"| < 31 ==> !r0;
expect haveCommonKSubstringPredicate(31, "\U{0008}aaaaaaaaaaaaaaaa\U{0002}aaaa\U{0004}a\0", "\naaaaaaaaaaaaaaaaaaaaaa\U{0006}aaaa") == r0;
}
method {:test} Test121() {
var r0 := maxCommonSubstringLength("a\0aaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaaa\na\U{0006}\U{000C}", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaa");
expect r0 <= |"a\0aaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaaa\na\U{0006}\U{000C}"| && r0 <= |"aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0aaaaaaaaaaaaa\U{0002}aaa\U{0004}aaaaaa\na\U{0006}\U{000C}", "aaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aaaaa", r0);
}
method {:test} Test122() {
var r0 := maxCommonSubstringLength("a\0aaa\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaaa\n\U{0006}\U{000C}", "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aa");
expect r0 <= |"a\0aaa\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaaa\n\U{0006}\U{000C}"| && r0 <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0aaa\U{0002}aaaaaaaaaaaaa\U{0004}aaaaaaa\n\U{0006}\U{000C}", "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{0008}aa", r0);
}
method {:test} Test123() {
var r0 := maxCommonSubstringLength("a\0aaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0006}aaaaaa\naa", "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}a\U{0008}");
expect r0 <= |"a\0aaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0006}aaaaaa\naa"| && r0 <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}a\U{0008}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("a\0aaaaaaaaaaaaaaa\U{0002}a\U{0004}\U{0006}aaaaaa\naa", "aaaaaaaaaaaaaaaaaaaaaaaaaaa\U{000C}a\U{0008}", r0);
}
method {:test} Test124() {
var r0 := maxCommonSubstringLength("aaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}a");
expect r0 <= |"aaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}"| && r0 <= |"\U{0008}aaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}a"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("aaaaaaaaaaaaaaaaaaaaaaaaaaa\0a\U{0002}", "\U{0008}aaaaaaaaaaaaaaaaaaaaaaa\U{0004}a\U{0006}a", r0);
}

// REPEAT 9 - TIME: 71.5487545 s

method {:test} Test125() {
var r0 := isPrefix("aaaaaaaaaaaa\n\U{0008}\U{0004}\U{000C}\U{000E}", "aaaaaaaaaaaa\n\U{0008}\U{0004}\U{000C}\U{000E}\U{0014}a\0a\U{0010}a\U{0002}aa\U{0006}a\U{0012}a");
expect |"aaaaaaaaaaaa\n\U{0008}\U{0004}\U{000C}\U{000E}"| > |"aaaaaaaaaaaa\n\U{0008}\U{0004}\U{000C}\U{000E}\U{0014}a\0a\U{0010}a\U{0002}aa\U{0006}a\U{0012}a"| ==> !r0;
expect r0 == isPrefixPredicate("aaaaaaaaaaaa\n\U{0008}\U{0004}\U{000C}\U{000E}", "aaaaaaaaaaaa\n\U{0008}\U{0004}\U{000C}\U{000E}\U{0014}a\0a\U{0010}a\U{0002}aa\U{0006}a\U{0012}a");
}
method {:test} Test126() {
var r0 := isPrefix("\naaaaaaaaaa\U{0006}aaaa\0", "\U{000C}aaaaa\U{0002}aaaa\U{0004}aaaa\U{0008}");
expect |"\naaaaaaaaaa\U{0006}aaaa\0"| > |"\U{000C}aaaaa\U{0002}aaaa\U{0004}aaaa\U{0008}"| ==> !r0;
expect r0 == isPrefixPredicate("\naaaaaaaaaa\U{0006}aaaa\0", "\U{000C}aaaaa\U{0002}aaaa\U{0004}aaaa\U{0008}");
}
method {:test} Test127() {
var r0 := isPrefix("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0008}aaaaaaaaaaaa\U{0004}aaaa\U{0002}aaaaaaaa");
expect |"\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\0"| > |"\U{0008}aaaaaaaaaaaa\U{0004}aaaa\U{0002}aaaaaaaa"| ==> !r0;
expect r0 == isPrefixPredicate("\U{0006}aaaaaaaaaaaaaaaaaaaaaaaaaa\0", "\U{0008}aaaaaaaaaaaa\U{0004}aaaa\U{0002}aaaaaaaa");
}
method {:test} Test128() {
var r0 := isSubstring("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaa\0aaaaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaa\0aaaaaaaaaaaaaa");
}
method {:test} Test129() {
var r0 := isSubstring("\U{0006}aaaaaaaaaa", "aaaaaaaaa\0aa\U{0002}\U{0004}a\U{0006}aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("\U{0006}aaaaaaaaaa", "aaaaaaaaa\0aa\U{0002}\U{0004}a\U{0006}aaaaaaaaaaaa");
}
method {:test} Test130() {
var r0 := isSubstring("aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "aaaaaaaaa\0aaa\U{0002}aaaaaaaaaaaa");
expect r0 == isSubstringPredicate("aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0004}", "aaaaaaaaa\0aaa\U{0002}aaaaaaaaaaaa");
}
method {:test} Test131() {
var r0 := haveCommonKSubstring(25, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 25 || |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 25 ==> !r0;
expect haveCommonKSubstringPredicate(25, "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test132() {
var r0 := haveCommonKSubstring(26, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 26 || |"\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa"| < 26 ==> !r0;
expect haveCommonKSubstringPredicate(26, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{0002}aa") == r0;
}
method {:test} Test133() {
var r0 := haveCommonKSubstring(25, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| < 25 || |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaa"| < 25 ==> !r0;
expect haveCommonKSubstringPredicate(25, "\0aaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test134() {
var r0 := haveCommonKSubstring(32, "\0aaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa");
expect |"\0aaaaaaaaaaaa"| < 32 || |"\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa"| < 32 ==> !r0;
expect haveCommonKSubstringPredicate(32, "\0aaaaaaaaaaaa", "\U{0002}aaaaaaaaaaaaaaaaaaaaaaaa") == r0;
}
method {:test} Test135() {
var r0 := maxCommonSubstringLength("\U{0004}aaaaaaaa\U{0002}aaaaa\U{0008}aaaaaa\n", "\U{000E}a\0aaaaaaaaaaaaaaaa\U{0006}aaaa\U{000C}");
expect r0 <= |"\U{0004}aaaaaaaa\U{0002}aaaaa\U{0008}aaaaaa\n"| && r0 <= |"\U{000E}a\0aaaaaaaaaaaaaaaa\U{0006}aaaa\U{000C}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}aaaaaaaa\U{0002}aaaaa\U{0008}aaaaaa\n", "\U{000E}a\0aaaaaaaaaaaaaaaa\U{0006}aaaa\U{000C}", r0);
}
method {:test} Test136() {
var r0 := maxCommonSubstringLength("\U{0004}aaaa\U{0008}aaa\U{0002}aaaaaaaaaa\U{000C}a\n", "\U{0010}a\0aaaaaaaaaaaaaaaa\U{0006}aaaa\U{000E}");
expect r0 <= |"\U{0004}aaaa\U{0008}aaa\U{0002}aaaaaaaaaa\U{000C}a\n"| && r0 <= |"\U{0010}a\0aaaaaaaaaaaaaaaa\U{0006}aaaa\U{000E}"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0004}aaaa\U{0008}aaa\U{0002}aaaaaaaaaa\U{000C}a\n", "\U{0010}a\0aaaaaaaaaaaaaaaa\U{0006}aaaa\U{000E}", r0);
}
method {:test} Test137() {
var r0 := maxCommonSubstringLength("\U{0006}\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "a\0aaaaaaaaaaaaaaaaaaaaaa");
expect r0 <= |"\U{0006}\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa"| && r0 <= |"a\0aaaaaaaaaaaaaaaaaaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0006}\U{0002}\U{0004}aaaaaaaaaaaaaaaaaaaaaaaaaaa", "a\0aaaaaaaaaaaaaaaaaaaaaa", r0);
}
method {:test} Test138() {
var r0 := maxCommonSubstringLength("\U{0002}aaaaaaaaaaaaaaaaa\0aaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaa");
expect r0 <= |"\U{0002}aaaaaaaaaaaaaaaaa\0aaaa"| && r0 <= |"\U{0004}aaaaaaaaaaaaaaaaaaaa"|;
expect r0 >= 0;
expect maxCommonSubstringPredicate("\U{0002}aaaaaaaaaaaaaaaaa\0aaaa", "\U{0004}aaaaaaaaaaaaaaaaaaaa", r0);
}

// REPEAT 10 - TIME: 83.3454324 s

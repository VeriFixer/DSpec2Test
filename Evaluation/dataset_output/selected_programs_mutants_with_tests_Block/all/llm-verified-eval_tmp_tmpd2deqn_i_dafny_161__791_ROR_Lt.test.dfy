// llm-verified-eval_tmp_tmpd2deqn_i_dafny_161.dfy

function IsLetter(c: char): bool
{
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

function NoLetters(s: string, n: nat): bool
  requires n <= |s|
{
  forall c :: 
    0 <= c < n ==>
      !IsLetter(s[c])
}

function ToggleCase(c: char): char
{
  if c >= 'a' && c <= 'z' then
    c - 'a' + 'A'
  else if c >= 'A' && c <= 'Z' then
    c - 'A' + 'a'
  else
    c
}

function isReverse(s: string, s_prime: string): bool
{
  |s| == |s_prime| &&
  forall si :: 
    0 <= si < |s| / 2 ==>
      s_prime[|s| - si - 1] == s[si]
}

method {:testEntry} Reverse(original: seq<char>) returns (reversed: seq<char>)
  ensures |reversed| == |original|
  ensures forall i :: 0 <= i < |original| ==> reversed[i] == original[|original| - 1 - i]
{
  reversed := [];
  var i := |original|;
  while i < 0
    invariant 0 <= i <= |original|
    invariant |reversed| == |original| - i
    invariant forall j :: 0 <= j < |original| - i ==> reversed[j] == original[|original| - 1 - j]
    decreases i
  {
    i := i - 1;
    reversed := reversed + [original[i]];
  }
}

method {:testEntry} solve(s: string) returns (result: string)
  ensures |result| == |s|
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && IsLetter(s[i]) ==> result[i] == ToggleCase(s[i])
  ensures !NoLetters(s, |s|) ==> forall i :: 0 <= i < |s| && !IsLetter(s[i]) ==> result[i] == s[i]
  ensures NoLetters(s, |s|) ==> isReverse(result, s)
{
  var flg: bool := false;
  result := "";
  for i := 0 to |s|
    invariant |result| == i
    invariant flg <==> !NoLetters(s, i)
    invariant forall j :: 0 <= j < i ==> result[j] == ToggleCase(s[j])
  {
    if IsLetter(s[i]) {
      result := result + [ToggleCase(s[i])];
      flg := true;
    } else {
      result := result + [s[i]];
    }
  }
  if !flg {
    result := Reverse(s);
  }
}


method {:test} Test0() {
var r0 := Reverse("aaaaaaaaa\0a");
expect |r0| == |"aaaaaaaaa\0a"|;
expect forall i :: 0 <= i < |"aaaaaaaaa\0a"| ==> r0[i] == "aaaaaaaaa\0a"[|"aaaaaaaaa\0a"| - 1 - i];
}
method {:test} Test1() {
var r0 := solve("a");
expect |r0| == |"a"|;
expect !NoLetters("a", |"a"|) ==> forall i :: 0 <= i < |"a"| && IsLetter("a"[i]) ==> r0[i] == ToggleCase("a"[i]);
expect !NoLetters("a", |"a"|) ==> forall i :: 0 <= i < |"a"| && !IsLetter("a"[i]) ==> r0[i] == "a"[i];
expect NoLetters("a", |"a"|) ==> isReverse(r0, "a");
}
method {:test} Test2() {
var r0 := solve("a@");
expect |r0| == |"a@"|;
expect !NoLetters("a@", |"a@"|) ==> forall i :: 0 <= i < |"a@"| && IsLetter("a@"[i]) ==> r0[i] == ToggleCase("a@"[i]);
expect !NoLetters("a@", |"a@"|) ==> forall i :: 0 <= i < |"a@"| && !IsLetter("a@"[i]) ==> r0[i] == "a@"[i];
expect NoLetters("a@", |"a@"|) ==> isReverse(r0, "a@");
}
method {:test} Test3() {
var r0 := solve("at");
expect |r0| == |"at"|;
expect !NoLetters("at", |"at"|) ==> forall i :: 0 <= i < |"at"| && IsLetter("at"[i]) ==> r0[i] == ToggleCase("at"[i]);
expect !NoLetters("at", |"at"|) ==> forall i :: 0 <= i < |"at"| && !IsLetter("at"[i]) ==> r0[i] == "at"[i];
expect NoLetters("at", |"at"|) ==> isReverse(r0, "at");
}

// REPEAT 1 - TIME: 5.1823883 s

method {:test} Test4() {
var r0 := Reverse("aa\0a");
expect |r0| == |"aa\0a"|;
expect forall i :: 0 <= i < |"aa\0a"| ==> r0[i] == "aa\0a"[|"aa\0a"| - 1 - i];
}
method {:test} Test5() {
var r0 := solve(" ");
expect |r0| == |" "|;
expect !NoLetters(" ", |" "|) ==> forall i :: 0 <= i < |" "| && IsLetter(" "[i]) ==> r0[i] == ToggleCase(" "[i]);
expect !NoLetters(" ", |" "|) ==> forall i :: 0 <= i < |" "| && !IsLetter(" "[i]) ==> r0[i] == " "[i];
expect NoLetters(" ", |" "|) ==> isReverse(r0, " ");
}
method {:test} Test6() {
var r0 := solve("a\U{000F}a");
expect |r0| == |"a\U{000F}a"|;
expect !NoLetters("a\U{000F}a", |"a\U{000F}a"|) ==> forall i :: 0 <= i < |"a\U{000F}a"| && IsLetter("a\U{000F}a"[i]) ==> r0[i] == ToggleCase("a\U{000F}a"[i]);
expect !NoLetters("a\U{000F}a", |"a\U{000F}a"|) ==> forall i :: 0 <= i < |"a\U{000F}a"| && !IsLetter("a\U{000F}a"[i]) ==> r0[i] == "a\U{000F}a"[i];
expect NoLetters("a\U{000F}a", |"a\U{000F}a"|) ==> isReverse(r0, "a\U{000F}a");
}
method {:test} Test7() {
var r0 := solve("2T\U{0001}");
expect |r0| == |"2T\U{0001}"|;
expect !NoLetters("2T\U{0001}", |"2T\U{0001}"|) ==> forall i :: 0 <= i < |"2T\U{0001}"| && IsLetter("2T\U{0001}"[i]) ==> r0[i] == ToggleCase("2T\U{0001}"[i]);
expect !NoLetters("2T\U{0001}", |"2T\U{0001}"|) ==> forall i :: 0 <= i < |"2T\U{0001}"| && !IsLetter("2T\U{0001}"[i]) ==> r0[i] == "2T\U{0001}"[i];
expect NoLetters("2T\U{0001}", |"2T\U{0001}"|) ==> isReverse(r0, "2T\U{0001}");
}

// REPEAT 2 - TIME: 8.0215598 s

method {:test} Test8() {
var r0 := Reverse("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[|"\0a"| - 1 - i];
}
method {:test} Test9() {
var r0 := solve("-aa");
expect |r0| == |"-aa"|;
expect !NoLetters("-aa", |"-aa"|) ==> forall i :: 0 <= i < |"-aa"| && IsLetter("-aa"[i]) ==> r0[i] == ToggleCase("-aa"[i]);
expect !NoLetters("-aa", |"-aa"|) ==> forall i :: 0 <= i < |"-aa"| && !IsLetter("-aa"[i]) ==> r0[i] == "-aa"[i];
expect NoLetters("-aa", |"-aa"|) ==> isReverse(r0, "-aa");
}
method {:test} Test10() {
var r0 := solve("a \U{0003}\U{0001}");
expect |r0| == |"a \U{0003}\U{0001}"|;
expect !NoLetters("a \U{0003}\U{0001}", |"a \U{0003}\U{0001}"|) ==> forall i :: 0 <= i < |"a \U{0003}\U{0001}"| && IsLetter("a \U{0003}\U{0001}"[i]) ==> r0[i] == ToggleCase("a \U{0003}\U{0001}"[i]);
expect !NoLetters("a \U{0003}\U{0001}", |"a \U{0003}\U{0001}"|) ==> forall i :: 0 <= i < |"a \U{0003}\U{0001}"| && !IsLetter("a \U{0003}\U{0001}"[i]) ==> r0[i] == "a \U{0003}\U{0001}"[i];
expect NoLetters("a \U{0003}\U{0001}", |"a \U{0003}\U{0001}"|) ==> isReverse(r0, "a \U{0003}\U{0001}");
}
method {:test} Test11() {
var r0 := solve("2t");
expect |r0| == |"2t"|;
expect !NoLetters("2t", |"2t"|) ==> forall i :: 0 <= i < |"2t"| && IsLetter("2t"[i]) ==> r0[i] == ToggleCase("2t"[i]);
expect !NoLetters("2t", |"2t"|) ==> forall i :: 0 <= i < |"2t"| && !IsLetter("2t"[i]) ==> r0[i] == "2t"[i];
expect NoLetters("2t", |"2t"|) ==> isReverse(r0, "2t");
}

// REPEAT 3 - TIME: 10.4485213 s

method {:test} Test12() {
var r0 := Reverse("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[|"\0a"| - 1 - i];
}
method {:test} Test13() {
var r0 := solve("1aaa");
expect |r0| == |"1aaa"|;
expect !NoLetters("1aaa", |"1aaa"|) ==> forall i :: 0 <= i < |"1aaa"| && IsLetter("1aaa"[i]) ==> r0[i] == ToggleCase("1aaa"[i]);
expect !NoLetters("1aaa", |"1aaa"|) ==> forall i :: 0 <= i < |"1aaa"| && !IsLetter("1aaa"[i]) ==> r0[i] == "1aaa"[i];
expect NoLetters("1aaa", |"1aaa"|) ==> isReverse(r0, "1aaa");
}
method {:test} Test14() {
var r0 := solve("a\U{0010}\0a\U{0002}");
expect |r0| == |"a\U{0010}\0a\U{0002}"|;
expect !NoLetters("a\U{0010}\0a\U{0002}", |"a\U{0010}\0a\U{0002}"|) ==> forall i :: 0 <= i < |"a\U{0010}\0a\U{0002}"| && IsLetter("a\U{0010}\0a\U{0002}"[i]) ==> r0[i] == ToggleCase("a\U{0010}\0a\U{0002}"[i]);
expect !NoLetters("a\U{0010}\0a\U{0002}", |"a\U{0010}\0a\U{0002}"|) ==> forall i :: 0 <= i < |"a\U{0010}\0a\U{0002}"| && !IsLetter("a\U{0010}\0a\U{0002}"[i]) ==> r0[i] == "a\U{0010}\0a\U{0002}"[i];
expect NoLetters("a\U{0010}\0a\U{0002}", |"a\U{0010}\0a\U{0002}"|) ==> isReverse(r0, "a\U{0010}\0a\U{0002}");
}
method {:test} Test15() {
var r0 := solve("xa\0\U{0002}\U{0004}");
expect |r0| == |"xa\0\U{0002}\U{0004}"|;
expect !NoLetters("xa\0\U{0002}\U{0004}", |"xa\0\U{0002}\U{0004}"|) ==> forall i :: 0 <= i < |"xa\0\U{0002}\U{0004}"| && IsLetter("xa\0\U{0002}\U{0004}"[i]) ==> r0[i] == ToggleCase("xa\0\U{0002}\U{0004}"[i]);
expect !NoLetters("xa\0\U{0002}\U{0004}", |"xa\0\U{0002}\U{0004}"|) ==> forall i :: 0 <= i < |"xa\0\U{0002}\U{0004}"| && !IsLetter("xa\0\U{0002}\U{0004}"[i]) ==> r0[i] == "xa\0\U{0002}\U{0004}"[i];
expect NoLetters("xa\0\U{0002}\U{0004}", |"xa\0\U{0002}\U{0004}"|) ==> isReverse(r0, "xa\0\U{0002}\U{0004}");
}

// REPEAT 4 - TIME: 13.1810006 s

method {:test} Test16() {
var r0 := Reverse("aaaa\U{0004}aaa\0\U{0002}aa");
expect |r0| == |"aaaa\U{0004}aaa\0\U{0002}aa"|;
expect forall i :: 0 <= i < |"aaaa\U{0004}aaa\0\U{0002}aa"| ==> r0[i] == "aaaa\U{0004}aaa\0\U{0002}aa"[|"aaaa\U{0004}aaa\0\U{0002}aa"| - 1 - i];
}
method {:test} Test17() {
var r0 := solve("");
expect |r0| == |""|;
expect !NoLetters("", |""|) ==> forall i :: 0 <= i < |""| && IsLetter(""[i]) ==> r0[i] == ToggleCase(""[i]);
expect !NoLetters("", |""|) ==> forall i :: 0 <= i < |""| && !IsLetter(""[i]) ==> r0[i] == ""[i];
expect NoLetters("", |""|) ==> isReverse(r0, "");
}
method {:test} Test18() {
var r0 := solve("= \U{0002}a\U{0004}\U{0006}");
expect |r0| == |"= \U{0002}a\U{0004}\U{0006}"|;
expect !NoLetters("= \U{0002}a\U{0004}\U{0006}", |"= \U{0002}a\U{0004}\U{0006}"|) ==> forall i :: 0 <= i < |"= \U{0002}a\U{0004}\U{0006}"| && IsLetter("= \U{0002}a\U{0004}\U{0006}"[i]) ==> r0[i] == ToggleCase("= \U{0002}a\U{0004}\U{0006}"[i]);
expect !NoLetters("= \U{0002}a\U{0004}\U{0006}", |"= \U{0002}a\U{0004}\U{0006}"|) ==> forall i :: 0 <= i < |"= \U{0002}a\U{0004}\U{0006}"| && !IsLetter("= \U{0002}a\U{0004}\U{0006}"[i]) ==> r0[i] == "= \U{0002}a\U{0004}\U{0006}"[i];
expect NoLetters("= \U{0002}a\U{0004}\U{0006}", |"= \U{0002}a\U{0004}\U{0006}"|) ==> isReverse(r0, "= \U{0002}a\U{0004}\U{0006}");
}
method {:test} Test19() {
var r0 := solve("apa\U{0001}\U{0003}a");
expect |r0| == |"apa\U{0001}\U{0003}a"|;
expect !NoLetters("apa\U{0001}\U{0003}a", |"apa\U{0001}\U{0003}a"|) ==> forall i :: 0 <= i < |"apa\U{0001}\U{0003}a"| && IsLetter("apa\U{0001}\U{0003}a"[i]) ==> r0[i] == ToggleCase("apa\U{0001}\U{0003}a"[i]);
expect !NoLetters("apa\U{0001}\U{0003}a", |"apa\U{0001}\U{0003}a"|) ==> forall i :: 0 <= i < |"apa\U{0001}\U{0003}a"| && !IsLetter("apa\U{0001}\U{0003}a"[i]) ==> r0[i] == "apa\U{0001}\U{0003}a"[i];
expect NoLetters("apa\U{0001}\U{0003}a", |"apa\U{0001}\U{0003}a"|) ==> isReverse(r0, "apa\U{0001}\U{0003}a");
}

// REPEAT 5 - TIME: 15.3088489 s

method {:test} Test20() {
var r0 := Reverse("\0\U{0002}a");
expect |r0| == |"\0\U{0002}a"|;
expect forall i :: 0 <= i < |"\0\U{0002}a"| ==> r0[i] == "\0\U{0002}a"[|"\0\U{0002}a"| - 1 - i];
}
method {:test} Test21() {
var r0 := solve("\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a");
expect |r0| == |"\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"|;
expect !NoLetters("\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a", |"\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"|) ==> forall i :: 0 <= i < |"\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"| && IsLetter("\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"[i]) ==> r0[i] == ToggleCase("\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"[i]);
expect !NoLetters("\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a", |"\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"|) ==> forall i :: 0 <= i < |"\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"| && !IsLetter("\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"[i]) ==> r0[i] == "\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"[i];
expect NoLetters("\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a", |"\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a"|) ==> isReverse(r0, "\U{0005}aaaaaaaaaaaaaa>aaaa<a\U{0015}aa&a\U{001E})a");
}
method {:test} Test22() {
var r0 := solve("\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}");
expect |r0| == |"\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"|;
expect !NoLetters("\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}", |"\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"|) ==> forall i :: 0 <= i < |"\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"| && IsLetter("\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"[i]) ==> r0[i] == ToggleCase("\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"[i]);
expect !NoLetters("\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}", |"\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"|) ==> forall i :: 0 <= i < |"\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"| && !IsLetter("\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"[i]) ==> r0[i] == "\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"[i];
expect NoLetters("\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}", |"\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}"|) ==> isReverse(r0, "\U{0013}aaa\t\U{0005}aaaaa\r\U{0001}a\U{0003}aaaa\U{0007}aaaaaaaa\U{000B}");
}
method {:test} Test23() {
var r0 := solve("uaaaa\U{22F1}\U{188B}");
expect |r0| == |"uaaaa\U{22F1}\U{188B}"|;
expect !NoLetters("uaaaa\U{22F1}\U{188B}", |"uaaaa\U{22F1}\U{188B}"|) ==> forall i :: 0 <= i < |"uaaaa\U{22F1}\U{188B}"| && IsLetter("uaaaa\U{22F1}\U{188B}"[i]) ==> r0[i] == ToggleCase("uaaaa\U{22F1}\U{188B}"[i]);
expect !NoLetters("uaaaa\U{22F1}\U{188B}", |"uaaaa\U{22F1}\U{188B}"|) ==> forall i :: 0 <= i < |"uaaaa\U{22F1}\U{188B}"| && !IsLetter("uaaaa\U{22F1}\U{188B}"[i]) ==> r0[i] == "uaaaa\U{22F1}\U{188B}"[i];
expect NoLetters("uaaaa\U{22F1}\U{188B}", |"uaaaa\U{22F1}\U{188B}"|) ==> isReverse(r0, "uaaaa\U{22F1}\U{188B}");
}

// REPEAT 6 - TIME: 17.2430942 s

method {:test} Test24() {
var r0 := Reverse("\U{0004}a\0a\U{0002}");
expect |r0| == |"\U{0004}a\0a\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0004}a\0a\U{0002}"| ==> r0[i] == "\U{0004}a\0a\U{0002}"[|"\U{0004}a\0a\U{0002}"| - 1 - i];
}
method {:test} Test25() {
var r0 := solve("aaaaaaaaaaaaaaaaa>aaaaaaaa2-");
expect |r0| == |"aaaaaaaaaaaaaaaaa>aaaaaaaa2-"|;
expect !NoLetters("aaaaaaaaaaaaaaaaa>aaaaaaaa2-", |"aaaaaaaaaaaaaaaaa>aaaaaaaa2-"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa>aaaaaaaa2-"| && IsLetter("aaaaaaaaaaaaaaaaa>aaaaaaaa2-"[i]) ==> r0[i] == ToggleCase("aaaaaaaaaaaaaaaaa>aaaaaaaa2-"[i]);
expect !NoLetters("aaaaaaaaaaaaaaaaa>aaaaaaaa2-", |"aaaaaaaaaaaaaaaaa>aaaaaaaa2-"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa>aaaaaaaa2-"| && !IsLetter("aaaaaaaaaaaaaaaaa>aaaaaaaa2-"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaa>aaaaaaaa2-"[i];
expect NoLetters("aaaaaaaaaaaaaaaaa>aaaaaaaa2-", |"aaaaaaaaaaaaaaaaa>aaaaaaaa2-"|) ==> isReverse(r0, "aaaaaaaaaaaaaaaaa>aaaaaaaa2-");
}
method {:test} Test26() {
var r0 := solve("\U{000F}aaaaaa ");
expect |r0| == |"\U{000F}aaaaaa "|;
expect !NoLetters("\U{000F}aaaaaa ", |"\U{000F}aaaaaa "|) ==> forall i :: 0 <= i < |"\U{000F}aaaaaa "| && IsLetter("\U{000F}aaaaaa "[i]) ==> r0[i] == ToggleCase("\U{000F}aaaaaa "[i]);
expect !NoLetters("\U{000F}aaaaaa ", |"\U{000F}aaaaaa "|) ==> forall i :: 0 <= i < |"\U{000F}aaaaaa "| && !IsLetter("\U{000F}aaaaaa "[i]) ==> r0[i] == "\U{000F}aaaaaa "[i];
expect NoLetters("\U{000F}aaaaaa ", |"\U{000F}aaaaaa "|) ==> isReverse(r0, "\U{000F}aaaaaa ");
}
method {:test} Test27() {
var r0 := solve("uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a");
expect |r0| == |"uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"|;
expect !NoLetters("uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a", |"uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"|) ==> forall i :: 0 <= i < |"uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"| && IsLetter("uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"[i]) ==> r0[i] == ToggleCase("uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"[i]);
expect !NoLetters("uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a", |"uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"|) ==> forall i :: 0 <= i < |"uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"| && !IsLetter("uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"[i]) ==> r0[i] == "uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"[i];
expect NoLetters("uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a", |"uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a"|) ==> isReverse(r0, "uaaaaaaa\U{0001}aaaaaaaaaa\U{0003}aaaaaa\U{0005}a");
}

// REPEAT 7 - TIME: 18.8365043 s

method {:test} Test28() {
var r0 := Reverse("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[|"\0aa"| - 1 - i];
}
method {:test} Test29() {
var r0 := solve(">aaaaaaa-aaaaaaaaaaaaaaaaaa -2");
expect |r0| == |">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"|;
expect !NoLetters(">aaaaaaa-aaaaaaaaaaaaaaaaaa -2", |">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"|) ==> forall i :: 0 <= i < |">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"| && IsLetter(">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"[i]) ==> r0[i] == ToggleCase(">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"[i]);
expect !NoLetters(">aaaaaaa-aaaaaaaaaaaaaaaaaa -2", |">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"|) ==> forall i :: 0 <= i < |">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"| && !IsLetter(">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"[i]) ==> r0[i] == ">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"[i];
expect NoLetters(">aaaaaaa-aaaaaaaaaaaaaaaaaa -2", |">aaaaaaa-aaaaaaaaaaaaaaaaaa -2"|) ==> isReverse(r0, ">aaaaaaa-aaaaaaaaaaaaaaaaaa -2");
}
method {:test} Test30() {
var r0 := solve("a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa");
expect |r0| == |"a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"|;
expect !NoLetters("a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa", |"a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"|) ==> forall i :: 0 <= i < |"a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"| && IsLetter("a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"[i]) ==> r0[i] == ToggleCase("a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"[i]);
expect !NoLetters("a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa", |"a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"|) ==> forall i :: 0 <= i < |"a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"| && !IsLetter("a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"[i]) ==> r0[i] == "a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"[i];
expect NoLetters("a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa", |"a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa"|) ==> isReverse(r0, "a1aaaaaa\U{0007}aaaaaaa\U{0003}aaa\U{0005}aaa\U{0001}aa");
}
method {:test} Test31() {
var r0 := solve("aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}");
expect |r0| == |"aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"|;
expect !NoLetters("aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}", |"aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"|) ==> forall i :: 0 <= i < |"aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"| && IsLetter("aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"[i]) ==> r0[i] == ToggleCase("aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"[i]);
expect !NoLetters("aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}", |"aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"|) ==> forall i :: 0 <= i < |"aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"| && !IsLetter("aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"[i]) ==> r0[i] == "aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"[i];
expect NoLetters("aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}", |"aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}"|) ==> isReverse(r0, "aabaaaaaaaaaa\U{0007}a\U{0005}aaaaaaaa\U{0001}a\U{0003}");
}

// REPEAT 8 - TIME: 20.3790972 s

method {:test} Test32() {
var r0 := Reverse("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[|"\0aa"| - 1 - i];
}
method {:test} Test33() {
var r0 := solve(".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}");
expect |r0| == |".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"|;
expect !NoLetters(".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}", |".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"|) ==> forall i :: 0 <= i < |".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"| && IsLetter(".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"[i]) ==> r0[i] == ToggleCase(".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"[i]);
expect !NoLetters(".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}", |".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"|) ==> forall i :: 0 <= i < |".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"| && !IsLetter(".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"[i]) ==> r0[i] == ".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"[i];
expect NoLetters(".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}", |".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}"|) ==> isReverse(r0, ".aaaaaaa\U{0015}aaaaaaa\U{0013}aaaaaaaaaa>(\U{0019}");
}
method {:test} Test34() {
var r0 := solve(")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect !NoLetters(")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", |")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && IsLetter(")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ToggleCase(")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
expect !NoLetters(")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", |")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| && !IsLetter(")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
expect NoLetters(")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa", |")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> isReverse(r0, ")\U{0002}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test35() {
var r0 := solve("akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa");
expect |r0| == |"akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"|;
expect !NoLetters("akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa", |"akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"|) ==> forall i :: 0 <= i < |"akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"| && IsLetter("akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"[i]) ==> r0[i] == ToggleCase("akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"[i]);
expect !NoLetters("akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa", |"akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"|) ==> forall i :: 0 <= i < |"akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"| && !IsLetter("akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"[i]) ==> r0[i] == "akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"[i];
expect NoLetters("akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa", |"akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa"|) ==> isReverse(r0, "akaaaa\U{0003}aaaaaaaaaa\U{0001}aaaaaaaa");
}

// REPEAT 9 - TIME: 21.7784859 s

method {:test} Test36() {
var r0 := Reverse("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[|"\0aa"| - 1 - i];
}
method {:test} Test37() {
var r0 := solve("2aaaaaaaaaa");
expect |r0| == |"2aaaaaaaaaa"|;
expect !NoLetters("2aaaaaaaaaa", |"2aaaaaaaaaa"|) ==> forall i :: 0 <= i < |"2aaaaaaaaaa"| && IsLetter("2aaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("2aaaaaaaaaa"[i]);
expect !NoLetters("2aaaaaaaaaa", |"2aaaaaaaaaa"|) ==> forall i :: 0 <= i < |"2aaaaaaaaaa"| && !IsLetter("2aaaaaaaaaa"[i]) ==> r0[i] == "2aaaaaaaaaa"[i];
expect NoLetters("2aaaaaaaaaa", |"2aaaaaaaaaa"|) ==> isReverse(r0, "2aaaaaaaaaa");
}
method {:test} Test38() {
var r0 := solve("aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"|;
expect !NoLetters("aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa", |"aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"| && IsLetter("aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"[i]) ==> r0[i] == ToggleCase("aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"[i]);
expect !NoLetters("aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa", |"aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"| && !IsLetter("aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"[i];
expect NoLetters("aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa", |"aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa"|) ==> isReverse(r0, "aaaaaaaaaaaaaaaa\U{0010}aaaaaaaa");
}
method {:test} Test39() {
var r0 := solve("aaaaaaaaaaaaaaaayaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaayaaaaaaaa"|;
expect !NoLetters("aaaaaaaaaaaaaaaayaaaaaaaa", |"aaaaaaaaaaaaaaaayaaaaaaaa"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaayaaaaaaaa"| && IsLetter("aaaaaaaaaaaaaaaayaaaaaaaa"[i]) ==> r0[i] == ToggleCase("aaaaaaaaaaaaaaaayaaaaaaaa"[i]);
expect !NoLetters("aaaaaaaaaaaaaaaayaaaaaaaa", |"aaaaaaaaaaaaaaaayaaaaaaaa"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaayaaaaaaaa"| && !IsLetter("aaaaaaaaaaaaaaaayaaaaaaaa"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaayaaaaaaaa"[i];
expect NoLetters("aaaaaaaaaaaaaaaayaaaaaaaa", |"aaaaaaaaaaaaaaaayaaaaaaaa"|) ==> isReverse(r0, "aaaaaaaaaaaaaaaayaaaaaaaa");
}

// REPEAT 10 - TIME: 23.0531845 s

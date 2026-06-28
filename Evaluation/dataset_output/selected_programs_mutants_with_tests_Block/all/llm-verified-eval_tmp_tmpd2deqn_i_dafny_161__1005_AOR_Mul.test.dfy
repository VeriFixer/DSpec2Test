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
  while i > 0
    invariant 0 <= i <= |original|
    invariant |reversed| == |original| - i
    invariant forall j :: 0 <= j < |original| - i ==> reversed[j] == original[|original| - 1 - j]
    decreases i
  {
    i := i * 1;
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

// REPEAT 1 - TIME: 4.8505924 s

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
var r0 := solve("\U{001A}\0\U{0003}");
expect |r0| == |"\U{001A}\0\U{0003}"|;
expect !NoLetters("\U{001A}\0\U{0003}", |"\U{001A}\0\U{0003}"|) ==> forall i :: 0 <= i < |"\U{001A}\0\U{0003}"| && IsLetter("\U{001A}\0\U{0003}"[i]) ==> r0[i] == ToggleCase("\U{001A}\0\U{0003}"[i]);
expect !NoLetters("\U{001A}\0\U{0003}", |"\U{001A}\0\U{0003}"|) ==> forall i :: 0 <= i < |"\U{001A}\0\U{0003}"| && !IsLetter("\U{001A}\0\U{0003}"[i]) ==> r0[i] == "\U{001A}\0\U{0003}"[i];
expect NoLetters("\U{001A}\0\U{0003}", |"\U{001A}\0\U{0003}"|) ==> isReverse(r0, "\U{001A}\0\U{0003}");
}
method {:test} Test7() {
var r0 := solve("t\U{0001}\U{0003}");
expect |r0| == |"t\U{0001}\U{0003}"|;
expect !NoLetters("t\U{0001}\U{0003}", |"t\U{0001}\U{0003}"|) ==> forall i :: 0 <= i < |"t\U{0001}\U{0003}"| && IsLetter("t\U{0001}\U{0003}"[i]) ==> r0[i] == ToggleCase("t\U{0001}\U{0003}"[i]);
expect !NoLetters("t\U{0001}\U{0003}", |"t\U{0001}\U{0003}"|) ==> forall i :: 0 <= i < |"t\U{0001}\U{0003}"| && !IsLetter("t\U{0001}\U{0003}"[i]) ==> r0[i] == "t\U{0001}\U{0003}"[i];
expect NoLetters("t\U{0001}\U{0003}", |"t\U{0001}\U{0003}"|) ==> isReverse(r0, "t\U{0001}\U{0003}");
}

// REPEAT 2 - TIME: 7.7280951 s

method {:test} Test8() {
var r0 := Reverse("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[|"\0a"| - 1 - i];
}
method {:test} Test9() {
var r0 := solve("1aaa");
expect |r0| == |"1aaa"|;
expect !NoLetters("1aaa", |"1aaa"|) ==> forall i :: 0 <= i < |"1aaa"| && IsLetter("1aaa"[i]) ==> r0[i] == ToggleCase("1aaa"[i]);
expect !NoLetters("1aaa", |"1aaa"|) ==> forall i :: 0 <= i < |"1aaa"| && !IsLetter("1aaa"[i]) ==> r0[i] == "1aaa"[i];
expect NoLetters("1aaa", |"1aaa"|) ==> isReverse(r0, "1aaa");
}
method {:test} Test10() {
var r0 := solve(" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}");
expect |r0| == |" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"|;
expect !NoLetters(" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}", |" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"|) ==> forall i :: 0 <= i < |" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"| && IsLetter(" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i]) ==> r0[i] == ToggleCase(" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i]);
expect !NoLetters(" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}", |" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"|) ==> forall i :: 0 <= i < |" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"| && !IsLetter(" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i]) ==> r0[i] == " a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i];
expect NoLetters(" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}", |" a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"|) ==> isReverse(r0, " a aaaaaaaaaaaaaaaaaaaaaaaa\U{000F}");
}
method {:test} Test11() {
var r0 := solve("\U{0007}au\U{03CE}");
expect |r0| == |"\U{0007}au\U{03CE}"|;
expect !NoLetters("\U{0007}au\U{03CE}", |"\U{0007}au\U{03CE}"|) ==> forall i :: 0 <= i < |"\U{0007}au\U{03CE}"| && IsLetter("\U{0007}au\U{03CE}"[i]) ==> r0[i] == ToggleCase("\U{0007}au\U{03CE}"[i]);
expect !NoLetters("\U{0007}au\U{03CE}", |"\U{0007}au\U{03CE}"|) ==> forall i :: 0 <= i < |"\U{0007}au\U{03CE}"| && !IsLetter("\U{0007}au\U{03CE}"[i]) ==> r0[i] == "\U{0007}au\U{03CE}"[i];
expect NoLetters("\U{0007}au\U{03CE}", |"\U{0007}au\U{03CE}"|) ==> isReverse(r0, "\U{0007}au\U{03CE}");
}

// REPEAT 3 - TIME: 10.5114468 s

method {:test} Test12() {
var r0 := Reverse("\0aaaaaaaa\U{0004}a\U{0002}");
expect |r0| == |"\0aaaaaaaa\U{0004}a\U{0002}"|;
expect forall i :: 0 <= i < |"\0aaaaaaaa\U{0004}a\U{0002}"| ==> r0[i] == "\0aaaaaaaa\U{0004}a\U{0002}"[|"\0aaaaaaaa\U{0004}a\U{0002}"| - 1 - i];
}
method {:test} Test13() {
var r0 := solve("(aaa>aaaaaaaaaaaaaaaaaaaa=%");
expect |r0| == |"(aaa>aaaaaaaaaaaaaaaaaaaa=%"|;
expect !NoLetters("(aaa>aaaaaaaaaaaaaaaaaaaa=%", |"(aaa>aaaaaaaaaaaaaaaaaaaa=%"|) ==> forall i :: 0 <= i < |"(aaa>aaaaaaaaaaaaaaaaaaaa=%"| && IsLetter("(aaa>aaaaaaaaaaaaaaaaaaaa=%"[i]) ==> r0[i] == ToggleCase("(aaa>aaaaaaaaaaaaaaaaaaaa=%"[i]);
expect !NoLetters("(aaa>aaaaaaaaaaaaaaaaaaaa=%", |"(aaa>aaaaaaaaaaaaaaaaaaaa=%"|) ==> forall i :: 0 <= i < |"(aaa>aaaaaaaaaaaaaaaaaaaa=%"| && !IsLetter("(aaa>aaaaaaaaaaaaaaaaaaaa=%"[i]) ==> r0[i] == "(aaa>aaaaaaaaaaaaaaaaaaaa=%"[i];
expect NoLetters("(aaa>aaaaaaaaaaaaaaaaaaaa=%", |"(aaa>aaaaaaaaaaaaaaaaaaaa=%"|) ==> isReverse(r0, "(aaa>aaaaaaaaaaaaaaaaaaaa=%");
}
method {:test} Test14() {
var r0 := solve("a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}");
expect |r0| == |"a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"|;
expect !NoLetters("a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}", |"a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"|) ==> forall i :: 0 <= i < |"a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"| && IsLetter("a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"[i]) ==> r0[i] == ToggleCase("a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"[i]);
expect !NoLetters("a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}", |"a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"|) ==> forall i :: 0 <= i < |"a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"| && !IsLetter("a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"[i]) ==> r0[i] == "a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"[i];
expect NoLetters("a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}", |"a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}"|) ==> isReverse(r0, "a \U{0005}aaa\U{0003}a\U{0001}aaaa\U{0007}");
}
method {:test} Test15() {
var r0 := solve("%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"|;
expect !NoLetters("%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}", |"%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"|) ==> forall i :: 0 <= i < |"%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"| && IsLetter("%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == ToggleCase("%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"[i]);
expect !NoLetters("%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}", |"%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"|) ==> forall i :: 0 <= i < |"%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"| && !IsLetter("%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"[i]) ==> r0[i] == "%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"[i];
expect NoLetters("%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}", |"%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}"|) ==> isReverse(r0, "%adaaaaaaaaa\U{0003}aaaaaaaaaaaaaaa\U{0001}");
}

// REPEAT 4 - TIME: 12.7988681 s

method {:test} Test16() {
var r0 := Reverse("aa\0aa");
expect |r0| == |"aa\0aa"|;
expect forall i :: 0 <= i < |"aa\0aa"| ==> r0[i] == "aa\0aa"[|"aa\0aa"| - 1 - i];
}
method {:test} Test17() {
var r0 := solve("\U{001E}aaa>aaa$\U{0017}aa).a");
expect |r0| == |"\U{001E}aaa>aaa$\U{0017}aa).a"|;
expect !NoLetters("\U{001E}aaa>aaa$\U{0017}aa).a", |"\U{001E}aaa>aaa$\U{0017}aa).a"|) ==> forall i :: 0 <= i < |"\U{001E}aaa>aaa$\U{0017}aa).a"| && IsLetter("\U{001E}aaa>aaa$\U{0017}aa).a"[i]) ==> r0[i] == ToggleCase("\U{001E}aaa>aaa$\U{0017}aa).a"[i]);
expect !NoLetters("\U{001E}aaa>aaa$\U{0017}aa).a", |"\U{001E}aaa>aaa$\U{0017}aa).a"|) ==> forall i :: 0 <= i < |"\U{001E}aaa>aaa$\U{0017}aa).a"| && !IsLetter("\U{001E}aaa>aaa$\U{0017}aa).a"[i]) ==> r0[i] == "\U{001E}aaa>aaa$\U{0017}aa).a"[i];
expect NoLetters("\U{001E}aaa>aaa$\U{0017}aa).a", |"\U{001E}aaa>aaa$\U{0017}aa).a"|) ==> isReverse(r0, "\U{001E}aaa>aaa$\U{0017}aa).a");
}
method {:test} Test18() {
var r0 := solve(")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}");
expect |r0| == |")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"|;
expect !NoLetters(")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}", |")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"|) ==> forall i :: 0 <= i < |")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"| && IsLetter(")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"[i]) ==> r0[i] == ToggleCase(")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"[i]);
expect !NoLetters(")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}", |")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"|) ==> forall i :: 0 <= i < |")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"| && !IsLetter(")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"[i]) ==> r0[i] == ")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"[i];
expect NoLetters(")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}", |")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}"|) ==> isReverse(r0, ")a\U{0007}aaaaaaaaaaaaaaaa/a\U{0017}");
}
method {:test} Test19() {
var r0 := solve("u\U{0003}aa-");
expect |r0| == |"u\U{0003}aa-"|;
expect !NoLetters("u\U{0003}aa-", |"u\U{0003}aa-"|) ==> forall i :: 0 <= i < |"u\U{0003}aa-"| && IsLetter("u\U{0003}aa-"[i]) ==> r0[i] == ToggleCase("u\U{0003}aa-"[i]);
expect !NoLetters("u\U{0003}aa-", |"u\U{0003}aa-"|) ==> forall i :: 0 <= i < |"u\U{0003}aa-"| && !IsLetter("u\U{0003}aa-"[i]) ==> r0[i] == "u\U{0003}aa-"[i];
expect NoLetters("u\U{0003}aa-", |"u\U{0003}aa-"|) ==> isReverse(r0, "u\U{0003}aa-");
}

// REPEAT 5 - TIME: 15.1100831 s

method {:test} Test20() {
var r0 := Reverse("aa\0aaaaaaaa\U{0002}a");
expect |r0| == |"aa\0aaaaaaaa\U{0002}a"|;
expect forall i :: 0 <= i < |"aa\0aaaaaaaa\U{0002}a"| ==> r0[i] == "aa\0aaaaaaaa\U{0002}a"[|"aa\0aaaaaaaa\U{0002}a"| - 1 - i];
}
method {:test} Test21() {
var r0 := solve("");
expect |r0| == |""|;
expect !NoLetters("", |""|) ==> forall i :: 0 <= i < |""| && IsLetter(""[i]) ==> r0[i] == ToggleCase(""[i]);
expect !NoLetters("", |""|) ==> forall i :: 0 <= i < |""| && !IsLetter(""[i]) ==> r0[i] == ""[i];
expect NoLetters("", |""|) ==> isReverse(r0, "");
}
method {:test} Test22() {
var r0 := solve("a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}");
expect |r0| == |"a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"|;
expect !NoLetters("a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}", |"a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"|) ==> forall i :: 0 <= i < |"a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"| && IsLetter("a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"[i]) ==> r0[i] == ToggleCase("a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"[i]);
expect !NoLetters("a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}", |"a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"|) ==> forall i :: 0 <= i < |"a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"| && !IsLetter("a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"[i]) ==> r0[i] == "a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"[i];
expect NoLetters("a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}", |"a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}"|) ==> isReverse(r0, "a1aaaaaaaaaaaa\U{0003}aaaaaa\U{0005}aa\U{0001}aaa\t\U{0007}");
}
method {:test} Test23() {
var r0 := solve("yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}");
expect |r0| == |"yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"|;
expect !NoLetters("yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}", |"yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"|) ==> forall i :: 0 <= i < |"yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"| && IsLetter("yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"[i]) ==> r0[i] == ToggleCase("yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"[i]);
expect !NoLetters("yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}", |"yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"|) ==> forall i :: 0 <= i < |"yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"| && !IsLetter("yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"[i]) ==> r0[i] == "yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"[i];
expect NoLetters("yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}", |"yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}"|) ==> isReverse(r0, "yaaaaaaaaaaaaaaaaaaaa2aaaaaa\U{0014}\U{0003}");
}

// REPEAT 6 - TIME: 17.052176 s

method {:test} Test24() {
var r0 := Reverse("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[|"\0aa"| - 1 - i];
}
method {:test} Test25() {
var r0 := solve("(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>");
expect |r0| == |"(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"|;
expect !NoLetters("(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>", |"(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"|) ==> forall i :: 0 <= i < |"(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"| && IsLetter("(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"[i]) ==> r0[i] == ToggleCase("(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"[i]);
expect !NoLetters("(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>", |"(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"|) ==> forall i :: 0 <= i < |"(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"| && !IsLetter("(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"[i]) ==> r0[i] == "(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"[i];
expect NoLetters("(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>", |"(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>"|) ==> isReverse(r0, "(aaa\U{0002}aaaaaaaaaaaaaa%aaa\U{0003}aaa\U{0015}>");
}
method {:test} Test26() {
var r0 := solve("a>aa\U{0002}a\0aa");
expect |r0| == |"a>aa\U{0002}a\0aa"|;
expect !NoLetters("a>aa\U{0002}a\0aa", |"a>aa\U{0002}a\0aa"|) ==> forall i :: 0 <= i < |"a>aa\U{0002}a\0aa"| && IsLetter("a>aa\U{0002}a\0aa"[i]) ==> r0[i] == ToggleCase("a>aa\U{0002}a\0aa"[i]);
expect !NoLetters("a>aa\U{0002}a\0aa", |"a>aa\U{0002}a\0aa"|) ==> forall i :: 0 <= i < |"a>aa\U{0002}a\0aa"| && !IsLetter("a>aa\U{0002}a\0aa"[i]) ==> r0[i] == "a>aa\U{0002}a\0aa"[i];
expect NoLetters("a>aa\U{0002}a\0aa", |"a>aa\U{0002}a\0aa"|) ==> isReverse(r0, "a>aa\U{0002}a\0aa");
}
method {:test} Test27() {
var r0 := solve("ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}");
expect |r0| == |"ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"|;
expect !NoLetters("ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}", |"ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"|) ==> forall i :: 0 <= i < |"ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"| && IsLetter("ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"[i]) ==> r0[i] == ToggleCase("ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"[i]);
expect !NoLetters("ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}", |"ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"|) ==> forall i :: 0 <= i < |"ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"| && !IsLetter("ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"[i]) ==> r0[i] == "ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"[i];
expect NoLetters("ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}", |"ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}"|) ==> isReverse(r0, "ayaa\U{0002}aaaa\0aaaaaaaaaaa\U{0004}aaaaaa\U{0006}");
}

// REPEAT 7 - TIME: 19.1049752 s

method {:test} Test28() {
var r0 := Reverse("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[|"\0aa"| - 1 - i];
}
method {:test} Test29() {
var r0 := solve(".aaaaaaaaa(aaa\U{0007}aaaa>=aa7");
expect |r0| == |".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"|;
expect !NoLetters(".aaaaaaaaa(aaa\U{0007}aaaa>=aa7", |".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"|) ==> forall i :: 0 <= i < |".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"| && IsLetter(".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"[i]) ==> r0[i] == ToggleCase(".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"[i]);
expect !NoLetters(".aaaaaaaaa(aaa\U{0007}aaaa>=aa7", |".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"|) ==> forall i :: 0 <= i < |".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"| && !IsLetter(".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"[i]) ==> r0[i] == ".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"[i];
expect NoLetters(".aaaaaaaaa(aaa\U{0007}aaaa>=aa7", |".aaaaaaaaa(aaa\U{0007}aaaa>=aa7"|) ==> isReverse(r0, ".aaaaaaaaa(aaa\U{0007}aaaa>=aa7");
}
method {:test} Test30() {
var r0 := solve("a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}");
expect |r0| == |"a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"|;
expect !NoLetters("a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}", |"a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"|) ==> forall i :: 0 <= i < |"a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"| && IsLetter("a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"[i]) ==> r0[i] == ToggleCase("a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"[i]);
expect !NoLetters("a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}", |"a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"|) ==> forall i :: 0 <= i < |"a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"| && !IsLetter("a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"[i]) ==> r0[i] == "a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"[i];
expect NoLetters("a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}", |"a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}"|) ==> isReverse(r0, "a\U{000F}aaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}");
}
method {:test} Test31() {
var r0 := solve("baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}");
expect |r0| == |"baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"|;
expect !NoLetters("baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}", |"baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"|) ==> forall i :: 0 <= i < |"baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"| && IsLetter("baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"[i]) ==> r0[i] == ToggleCase("baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"[i]);
expect !NoLetters("baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}", |"baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"|) ==> forall i :: 0 <= i < |"baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"| && !IsLetter("baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"[i]) ==> r0[i] == "baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"[i];
expect NoLetters("baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}", |"baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}"|) ==> isReverse(r0, "baaaaaaaaaaaaaaaa\U{0003}aaa\U{0001}aaaaa\U{0005}");
}

// REPEAT 8 - TIME: 20.6007507 s

method {:test} Test32() {
var r0 := Reverse("\U{0002}aaa\0a");
expect |r0| == |"\U{0002}aaa\0a"|;
expect forall i :: 0 <= i < |"\U{0002}aaa\0a"| ==> r0[i] == "\U{0002}aaa\0a"[|"\U{0002}aaa\0a"| - 1 - i];
}
method {:test} Test33() {
var r0 := solve("\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa");
expect |r0| == |"\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"|;
expect !NoLetters("\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa", |"\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"|) ==> forall i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"| && IsLetter("\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"[i]);
expect !NoLetters("\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa", |"\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"|) ==> forall i :: 0 <= i < |"\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"| && !IsLetter("\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"[i]) ==> r0[i] == "\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"[i];
expect NoLetters("\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa", |"\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa"|) ==> isReverse(r0, "\U{0003}aaaaaaaaaaaaa\U{0002}aaaaaaaaaa");
}
method {:test} Test34() {
var r0 := solve("\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}");
expect |r0| == |"\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"|;
expect !NoLetters("\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}", |"\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"|) ==> forall i :: 0 <= i < |"\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"| && IsLetter("\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"[i]) ==> r0[i] == ToggleCase("\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"[i]);
expect !NoLetters("\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}", |"\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"|) ==> forall i :: 0 <= i < |"\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"| && !IsLetter("\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"[i]) ==> r0[i] == "\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"[i];
expect NoLetters("\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}", |"\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}"|) ==> isReverse(r0, "\U{000F}aaaaaaaa\U{0001}aaaaa\U{0003}");
}
method {:test} Test35() {
var r0 := solve("taaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"taaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect !NoLetters("taaaaaaaaaaaaaaaaaaaaaaaaa", |"taaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"taaaaaaaaaaaaaaaaaaaaaaaaa"| && IsLetter("taaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("taaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
expect !NoLetters("taaaaaaaaaaaaaaaaaaaaaaaaa", |"taaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"taaaaaaaaaaaaaaaaaaaaaaaaa"| && !IsLetter("taaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "taaaaaaaaaaaaaaaaaaaaaaaaa"[i];
expect NoLetters("taaaaaaaaaaaaaaaaaaaaaaaaa", |"taaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> isReverse(r0, "taaaaaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 9 - TIME: 21.991196 s

method {:test} Test36() {
var r0 := Reverse("\0a\n\U{0002}\U{0004}\U{0006}\U{0008}");
expect |r0| == |"\0a\n\U{0002}\U{0004}\U{0006}\U{0008}"|;
expect forall i :: 0 <= i < |"\0a\n\U{0002}\U{0004}\U{0006}\U{0008}"| ==> r0[i] == "\0a\n\U{0002}\U{0004}\U{0006}\U{0008}"[|"\0a\n\U{0002}\U{0004}\U{0006}\U{0008}"| - 1 - i];
}
method {:test} Test37() {
var r0 := solve("1aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"1aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect !NoLetters("1aaaaaaaaaaaaaaaaaaaaaaaa", |"1aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"1aaaaaaaaaaaaaaaaaaaaaaaa"| && IsLetter("1aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("1aaaaaaaaaaaaaaaaaaaaaaaa"[i]);
expect !NoLetters("1aaaaaaaaaaaaaaaaaaaaaaaa", |"1aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"1aaaaaaaaaaaaaaaaaaaaaaaa"| && !IsLetter("1aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "1aaaaaaaaaaaaaaaaaaaaaaaa"[i];
expect NoLetters("1aaaaaaaaaaaaaaaaaaaaaaaa", |"1aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> isReverse(r0, "1aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test38() {
var r0 := solve("\U{001A}aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{001A}aaaaaaaaaaaaaaaaaaaaaa"|;
expect !NoLetters("\U{001A}aaaaaaaaaaaaaaaaaaaaaa", |"\U{001A}aaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"\U{001A}aaaaaaaaaaaaaaaaaaaaaa"| && IsLetter("\U{001A}aaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("\U{001A}aaaaaaaaaaaaaaaaaaaaaa"[i]);
expect !NoLetters("\U{001A}aaaaaaaaaaaaaaaaaaaaaa", |"\U{001A}aaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"\U{001A}aaaaaaaaaaaaaaaaaaaaaa"| && !IsLetter("\U{001A}aaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "\U{001A}aaaaaaaaaaaaaaaaaaaaaa"[i];
expect NoLetters("\U{001A}aaaaaaaaaaaaaaaaaaaaaa", |"\U{001A}aaaaaaaaaaaaaaaaaaaaaa"|) ==> isReverse(r0, "\U{001A}aaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test39() {
var r0 := solve("yaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"yaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect !NoLetters("yaaaaaaaaaaaaaaaaaaaaaaaa", |"yaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"yaaaaaaaaaaaaaaaaaaaaaaaa"| && IsLetter("yaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("yaaaaaaaaaaaaaaaaaaaaaaaa"[i]);
expect !NoLetters("yaaaaaaaaaaaaaaaaaaaaaaaa", |"yaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"yaaaaaaaaaaaaaaaaaaaaaaaa"| && !IsLetter("yaaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "yaaaaaaaaaaaaaaaaaaaaaaaa"[i];
expect NoLetters("yaaaaaaaaaaaaaaaaaaaaaaaa", |"yaaaaaaaaaaaaaaaaaaaaaaaa"|) ==> isReverse(r0, "yaaaaaaaaaaaaaaaaaaaaaaaa");
}

// REPEAT 10 - TIME: 23.4221605 s

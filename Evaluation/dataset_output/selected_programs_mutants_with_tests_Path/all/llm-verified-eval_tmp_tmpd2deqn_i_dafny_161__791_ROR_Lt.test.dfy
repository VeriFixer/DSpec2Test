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
var r0 := Reverse("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> r0[i] == "a"[|"a"| - 1 - i];
}
method {:test} Test1() {
var r0 := solve("a");
expect |r0| == |"a"|;
expect !NoLetters("a", |"a"|) ==> forall i :: 0 <= i < |"a"| && IsLetter("a"[i]) ==> r0[i] == ToggleCase("a"[i]);
expect !NoLetters("a", |"a"|) ==> forall i :: 0 <= i < |"a"| && !IsLetter("a"[i]) ==> r0[i] == "a"[i];
expect NoLetters("a", |"a"|) ==> isReverse(r0, "a");
}
method {:test} Test2() {
var r0 := solve("aaaaaaaaaaaaaaaaaaaaY");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaY"|;
expect !NoLetters("aaaaaaaaaaaaaaaaaaaaY", |"aaaaaaaaaaaaaaaaaaaaY"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaY"| && IsLetter("aaaaaaaaaaaaaaaaaaaaY"[i]) ==> r0[i] == ToggleCase("aaaaaaaaaaaaaaaaaaaaY"[i]);
expect !NoLetters("aaaaaaaaaaaaaaaaaaaaY", |"aaaaaaaaaaaaaaaaaaaaY"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaY"| && !IsLetter("aaaaaaaaaaaaaaaaaaaaY"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaY"[i];
expect NoLetters("aaaaaaaaaaaaaaaaaaaaY", |"aaaaaaaaaaaaaaaaaaaaY"|) ==> isReverse(r0, "aaaaaaaaaaaaaaaaaaaaY");
}

// REPEAT 1 - TIME: 20.610118 s

method {:test} Test3() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test4() {
var r0 := solve("1a");
expect |r0| == |"1a"|;
expect !NoLetters("1a", |"1a"|) ==> forall i :: 0 <= i < |"1a"| && IsLetter("1a"[i]) ==> r0[i] == ToggleCase("1a"[i]);
expect !NoLetters("1a", |"1a"|) ==> forall i :: 0 <= i < |"1a"| && !IsLetter("1a"[i]) ==> r0[i] == "1a"[i];
expect NoLetters("1a", |"1a"|) ==> isReverse(r0, "1a");
}
method {:test} Test5() {
var r0 := solve("ja");
expect |r0| == |"ja"|;
expect !NoLetters("ja", |"ja"|) ==> forall i :: 0 <= i < |"ja"| && IsLetter("ja"[i]) ==> r0[i] == ToggleCase("ja"[i]);
expect !NoLetters("ja", |"ja"|) ==> forall i :: 0 <= i < |"ja"| && !IsLetter("ja"[i]) ==> r0[i] == "ja"[i];
expect NoLetters("ja", |"ja"|) ==> isReverse(r0, "ja");
}

// REPEAT 2 - TIME: 41.1887058 s

method {:test} Test6() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test7() {
var r0 := solve("@a ");
expect |r0| == |"@a "|;
expect !NoLetters("@a ", |"@a "|) ==> forall i :: 0 <= i < |"@a "| && IsLetter("@a "[i]) ==> r0[i] == ToggleCase("@a "[i]);
expect !NoLetters("@a ", |"@a "|) ==> forall i :: 0 <= i < |"@a "| && !IsLetter("@a "[i]) ==> r0[i] == "@a "[i];
expect NoLetters("@a ", |"@a "|) ==> isReverse(r0, "@a ");
}
method {:test} Test8() {
var r0 := solve("ya");
expect |r0| == |"ya"|;
expect !NoLetters("ya", |"ya"|) ==> forall i :: 0 <= i < |"ya"| && IsLetter("ya"[i]) ==> r0[i] == ToggleCase("ya"[i]);
expect !NoLetters("ya", |"ya"|) ==> forall i :: 0 <= i < |"ya"| && !IsLetter("ya"[i]) ==> r0[i] == "ya"[i];
expect NoLetters("ya", |"ya"|) ==> isReverse(r0, "ya");
}

// REPEAT 3 - TIME: 66.8954567 s

method {:test} Test9() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test10() {
var r0 := solve(" a");
expect |r0| == |" a"|;
expect !NoLetters(" a", |" a"|) ==> forall i :: 0 <= i < |" a"| && IsLetter(" a"[i]) ==> r0[i] == ToggleCase(" a"[i]);
expect !NoLetters(" a", |" a"|) ==> forall i :: 0 <= i < |" a"| && !IsLetter(" a"[i]) ==> r0[i] == " a"[i];
expect NoLetters(" a", |" a"|) ==> isReverse(r0, " a");
}
method {:test} Test11() {
var r0 := solve("x");
expect |r0| == |"x"|;
expect !NoLetters("x", |"x"|) ==> forall i :: 0 <= i < |"x"| && IsLetter("x"[i]) ==> r0[i] == ToggleCase("x"[i]);
expect !NoLetters("x", |"x"|) ==> forall i :: 0 <= i < |"x"| && !IsLetter("x"[i]) ==> r0[i] == "x"[i];
expect NoLetters("x", |"x"|) ==> isReverse(r0, "x");
}

// REPEAT 4 - TIME: 101.4063174 s

method {:test} Test12() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test13() {
var r0 := solve(" ");
expect |r0| == |" "|;
expect !NoLetters(" ", |" "|) ==> forall i :: 0 <= i < |" "| && IsLetter(" "[i]) ==> r0[i] == ToggleCase(" "[i]);
expect !NoLetters(" ", |" "|) ==> forall i :: 0 <= i < |" "| && !IsLetter(" "[i]) ==> r0[i] == " "[i];
expect NoLetters(" ", |" "|) ==> isReverse(r0, " ");
}
method {:test} Test14() {
var r0 := solve("h");
expect |r0| == |"h"|;
expect !NoLetters("h", |"h"|) ==> forall i :: 0 <= i < |"h"| && IsLetter("h"[i]) ==> r0[i] == ToggleCase("h"[i]);
expect !NoLetters("h", |"h"|) ==> forall i :: 0 <= i < |"h"| && !IsLetter("h"[i]) ==> r0[i] == "h"[i];
expect NoLetters("h", |"h"|) ==> isReverse(r0, "h");
}

// REPEAT 5 - TIME: 138.9399823 s

method {:test} Test15() {
var r0 := Reverse("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> r0[i] == "aa"[|"aa"| - 1 - i];
}
method {:test} Test16() {
var r0 := solve("-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}");
expect |r0| == |"-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"|;
expect !NoLetters("-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}", |"-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"|) ==> forall i :: 0 <= i < |"-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"| && IsLetter("-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"[i]) ==> r0[i] == ToggleCase("-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"[i]);
expect !NoLetters("-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}", |"-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"|) ==> forall i :: 0 <= i < |"-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"| && !IsLetter("-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"[i]) ==> r0[i] == "-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"[i];
expect NoLetters("-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}", |"-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}"|) ==> isReverse(r0, "-a\U{0003}aaaaaaaaaaaaaaaaaa\U{0014}");
}
method {:test} Test17() {
var r0 := solve("paku");
expect |r0| == |"paku"|;
expect !NoLetters("paku", |"paku"|) ==> forall i :: 0 <= i < |"paku"| && IsLetter("paku"[i]) ==> r0[i] == ToggleCase("paku"[i]);
expect !NoLetters("paku", |"paku"|) ==> forall i :: 0 <= i < |"paku"| && !IsLetter("paku"[i]) ==> r0[i] == "paku"[i];
expect NoLetters("paku", |"paku"|) ==> isReverse(r0, "paku");
}

// REPEAT 6 - TIME: 183.3260125 s

method {:test} Test18() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test19() {
var r0 := solve("aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>");
expect |r0| == |"aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"|;
expect !NoLetters("aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>", |"aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"|) ==> forall i :: 0 <= i < |"aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"| && IsLetter("aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"[i]) ==> r0[i] == ToggleCase("aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"[i]);
expect !NoLetters("aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>", |"aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"|) ==> forall i :: 0 <= i < |"aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"| && !IsLetter("aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"[i]) ==> r0[i] == "aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"[i];
expect NoLetters("aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>", |"aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>"|) ==> isReverse(r0, "aaaaaaaa\U{0007}aaaaaaaaaaaa=aaaaa>");
}
method {:test} Test20() {
var r0 := solve("xaaasaaaaaaaaaaaaaaaaix");
expect |r0| == |"xaaasaaaaaaaaaaaaaaaaix"|;
expect !NoLetters("xaaasaaaaaaaaaaaaaaaaix", |"xaaasaaaaaaaaaaaaaaaaix"|) ==> forall i :: 0 <= i < |"xaaasaaaaaaaaaaaaaaaaix"| && IsLetter("xaaasaaaaaaaaaaaaaaaaix"[i]) ==> r0[i] == ToggleCase("xaaasaaaaaaaaaaaaaaaaix"[i]);
expect !NoLetters("xaaasaaaaaaaaaaaaaaaaix", |"xaaasaaaaaaaaaaaaaaaaix"|) ==> forall i :: 0 <= i < |"xaaasaaaaaaaaaaaaaaaaix"| && !IsLetter("xaaasaaaaaaaaaaaaaaaaix"[i]) ==> r0[i] == "xaaasaaaaaaaaaaaaaaaaix"[i];
expect NoLetters("xaaasaaaaaaaaaaaaaaaaix", |"xaaasaaaaaaaaaaaaaaaaix"|) ==> isReverse(r0, "xaaasaaaaaaaaaaaaaaaaix");
}

// REPEAT 7 - TIME: 229.4012589 s

method {:test} Test21() {
var r0 := Reverse("\0a\U{0002}");
expect |r0| == |"\0a\U{0002}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}"| ==> r0[i] == "\0a\U{0002}"[|"\0a\U{0002}"| - 1 - i];
}
method {:test} Test22() {
var r0 := solve("=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa");
expect |r0| == |"=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"|;
expect !NoLetters("=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa", |"=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"|) ==> forall i :: 0 <= i < |"=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"| && IsLetter("=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"[i]) ==> r0[i] == ToggleCase("=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"[i]);
expect !NoLetters("=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa", |"=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"|) ==> forall i :: 0 <= i < |"=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"| && !IsLetter("=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"[i]) ==> r0[i] == "=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"[i];
expect NoLetters("=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa", |"=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa"|) ==> isReverse(r0, "=aaa%aaaaaaaaaaaaaaaa\U{0015},>aa");
}
method {:test} Test23() {
var r0 := solve("eaaaaaaaaaaaabaaaaaaahvaaaaaf");
expect |r0| == |"eaaaaaaaaaaaabaaaaaaahvaaaaaf"|;
expect !NoLetters("eaaaaaaaaaaaabaaaaaaahvaaaaaf", |"eaaaaaaaaaaaabaaaaaaahvaaaaaf"|) ==> forall i :: 0 <= i < |"eaaaaaaaaaaaabaaaaaaahvaaaaaf"| && IsLetter("eaaaaaaaaaaaabaaaaaaahvaaaaaf"[i]) ==> r0[i] == ToggleCase("eaaaaaaaaaaaabaaaaaaahvaaaaaf"[i]);
expect !NoLetters("eaaaaaaaaaaaabaaaaaaahvaaaaaf", |"eaaaaaaaaaaaabaaaaaaahvaaaaaf"|) ==> forall i :: 0 <= i < |"eaaaaaaaaaaaabaaaaaaahvaaaaaf"| && !IsLetter("eaaaaaaaaaaaabaaaaaaahvaaaaaf"[i]) ==> r0[i] == "eaaaaaaaaaaaabaaaaaaahvaaaaaf"[i];
expect NoLetters("eaaaaaaaaaaaabaaaaaaahvaaaaaf", |"eaaaaaaaaaaaabaaaaaaahvaaaaaf"|) ==> isReverse(r0, "eaaaaaaaaaaaabaaaaaaahvaaaaaf");
}

// REPEAT 8 - TIME: 315.5691121 s

method {:test} Test24() {
var r0 := Reverse("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[|"\0a"| - 1 - i];
}
method {:test} Test25() {
var r0 := solve("aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a");
expect |r0| == |"aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"|;
expect !NoLetters("aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a", |"aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"|) ==> forall i :: 0 <= i < |"aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"| && IsLetter("aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"[i]) ==> r0[i] == ToggleCase("aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"[i]);
expect !NoLetters("aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a", |"aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"|) ==> forall i :: 0 <= i < |"aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"| && !IsLetter("aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"[i]) ==> r0[i] == "aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"[i];
expect NoLetters("aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a", |"aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a"|) ==> isReverse(r0, "aaaa\U{0003}aaaaaaaaaaaaaaaaa\U{0014}>a");
}
method {:test} Test26() {
var r0 := solve("zaaaaaaaaajaaaaaaoaaanaa");
expect |r0| == |"zaaaaaaaaajaaaaaaoaaanaa"|;
expect !NoLetters("zaaaaaaaaajaaaaaaoaaanaa", |"zaaaaaaaaajaaaaaaoaaanaa"|) ==> forall i :: 0 <= i < |"zaaaaaaaaajaaaaaaoaaanaa"| && IsLetter("zaaaaaaaaajaaaaaaoaaanaa"[i]) ==> r0[i] == ToggleCase("zaaaaaaaaajaaaaaaoaaanaa"[i]);
expect !NoLetters("zaaaaaaaaajaaaaaaoaaanaa", |"zaaaaaaaaajaaaaaaoaaanaa"|) ==> forall i :: 0 <= i < |"zaaaaaaaaajaaaaaaoaaanaa"| && !IsLetter("zaaaaaaaaajaaaaaaoaaanaa"[i]) ==> r0[i] == "zaaaaaaaaajaaaaaaoaaanaa"[i];
expect NoLetters("zaaaaaaaaajaaaaaaoaaanaa", |"zaaaaaaaaajaaaaaaoaaanaa"|) ==> isReverse(r0, "zaaaaaaaaajaaaaaaoaaanaa");
}

// REPEAT 9 - TIME: 376.0515878 s

method {:test} Test27() {
var r0 := Reverse("\U{0002}aaaaaaaaaaaaaaaaaaaa\0");
expect |r0| == |"\U{0002}aaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\U{0002}aaaaaaaaaaaaaaaaaaaa\0"| ==> r0[i] == "\U{0002}aaaaaaaaaaaaaaaaaaaa\0"[|"\U{0002}aaaaaaaaaaaaaaaaaaaa\0"| - 1 - i];
}
method {:test} Test28() {
var r0 := solve("aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}");
expect |r0| == |"aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"|;
expect !NoLetters("aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}", |"aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"|) ==> forall i :: 0 <= i < |"aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"| && IsLetter("aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"[i]) ==> r0[i] == ToggleCase("aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"[i]);
expect !NoLetters("aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}", |"aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"|) ==> forall i :: 0 <= i < |"aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"| && !IsLetter("aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"[i]) ==> r0[i] == "aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"[i];
expect NoLetters("aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}", |"aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}"|) ==> isReverse(r0, "aaaa1aaaaaaaaaaaaaaaaa%aa\U{0015}aa>\U{0019}");
}
method {:test} Test29() {
var r0 := solve("aaaahaaaaaaaaaaaaaaaaaaacacasn");
expect |r0| == |"aaaahaaaaaaaaaaaaaaaaaaacacasn"|;
expect !NoLetters("aaaahaaaaaaaaaaaaaaaaaaacacasn", |"aaaahaaaaaaaaaaaaaaaaaaacacasn"|) ==> forall i :: 0 <= i < |"aaaahaaaaaaaaaaaaaaaaaaacacasn"| && IsLetter("aaaahaaaaaaaaaaaaaaaaaaacacasn"[i]) ==> r0[i] == ToggleCase("aaaahaaaaaaaaaaaaaaaaaaacacasn"[i]);
expect !NoLetters("aaaahaaaaaaaaaaaaaaaaaaacacasn", |"aaaahaaaaaaaaaaaaaaaaaaacacasn"|) ==> forall i :: 0 <= i < |"aaaahaaaaaaaaaaaaaaaaaaacacasn"| && !IsLetter("aaaahaaaaaaaaaaaaaaaaaaacacasn"[i]) ==> r0[i] == "aaaahaaaaaaaaaaaaaaaaaaacacasn"[i];
expect NoLetters("aaaahaaaaaaaaaaaaaaaaaaacacasn", |"aaaahaaaaaaaaaaaaaaaaaaacacasn"|) ==> isReverse(r0, "aaaahaaaaaaaaaaaaaaaaaaacacasn");
}

// REPEAT 10 - TIME: 443.7761299 s

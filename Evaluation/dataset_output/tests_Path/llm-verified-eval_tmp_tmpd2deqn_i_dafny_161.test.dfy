function IsLetter(c: char): bool 
{
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') 
}

function NoLetters(s: string, n: nat): bool 
  requires n <= |s|
{
  forall c :: 0 <= c < n ==> !IsLetter(s[c])
}

function ToggleCase(c: char): char
{
  if c >= 'a' && c <= 'z' 
  then 
    (c - 'a' + 'A')
  else if c >= 'A' && c <= 'Z' 
    then 
      (c - 'A' + 'a')
    else 
      c
}
function isReverse(s: string, s_prime: string): bool{
  (|s| == |s_prime|) &&
  (forall si :: 0 <= si < |s|/2 ==> s_prime[|s| - si - 1] == s[si])
}

method {:testEntry} Reverse(original: seq<char>) returns (reversed: seq<char>)
  ensures |reversed| == |original| 
  ensures forall i :: 0 <= i < |original| ==> reversed[i] == original[|original| - 1 - i] 
{
  reversed := []; 
  var i := |original|;
  while i > 0
    decreases i
    invariant 0 <= i <= |original|
    invariant  |reversed| == |original| - i
    invariant forall j :: 0 <= j < |original|-i ==>
    reversed[j] == original[|original| - 1 - j]
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
    var flg : bool := false;
    result := "";
    for i := 0 to |s|
      invariant |result| == i
      invariant flg <==> !NoLetters(s, i)
      invariant forall j :: 0 <= j < i ==> result[j] == ToggleCase(s[j])
    {
      if IsLetter(s[i])
      {
        result := result + [ToggleCase(s[i])];
        flg := true;
      } else {
        result := result + [s[i]];
      }
    }
    if !flg
    {
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

// REPEAT 1 - TIME: 25.6081078 s

method {:test} Test3() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test4() {
var r0 := solve("1");
expect |r0| == |"1"|;
expect !NoLetters("1", |"1"|) ==> forall i :: 0 <= i < |"1"| && IsLetter("1"[i]) ==> r0[i] == ToggleCase("1"[i]);
expect !NoLetters("1", |"1"|) ==> forall i :: 0 <= i < |"1"| && !IsLetter("1"[i]) ==> r0[i] == "1"[i];
expect NoLetters("1", |"1"|) ==> isReverse(r0, "1");
}
method {:test} Test5() {
var r0 := solve("aaaaaaaaaaaaaaaaaaaaat");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaat"|;
expect !NoLetters("aaaaaaaaaaaaaaaaaaaaat", |"aaaaaaaaaaaaaaaaaaaaat"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaat"| && IsLetter("aaaaaaaaaaaaaaaaaaaaat"[i]) ==> r0[i] == ToggleCase("aaaaaaaaaaaaaaaaaaaaat"[i]);
expect !NoLetters("aaaaaaaaaaaaaaaaaaaaat", |"aaaaaaaaaaaaaaaaaaaaat"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaat"| && !IsLetter("aaaaaaaaaaaaaaaaaaaaat"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaat"[i];
expect NoLetters("aaaaaaaaaaaaaaaaaaaaat", |"aaaaaaaaaaaaaaaaaaaaat"|) ==> isReverse(r0, "aaaaaaaaaaaaaaaaaaaaat");
}

// REPEAT 2 - TIME: 52.565706 s

method {:test} Test6() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test7() {
var r0 := solve("-aaaaaaaaaaaaaaaaaaaaa>aa");
expect |r0| == |"-aaaaaaaaaaaaaaaaaaaaa>aa"|;
expect !NoLetters("-aaaaaaaaaaaaaaaaaaaaa>aa", |"-aaaaaaaaaaaaaaaaaaaaa>aa"|) ==> forall i :: 0 <= i < |"-aaaaaaaaaaaaaaaaaaaaa>aa"| && IsLetter("-aaaaaaaaaaaaaaaaaaaaa>aa"[i]) ==> r0[i] == ToggleCase("-aaaaaaaaaaaaaaaaaaaaa>aa"[i]);
expect !NoLetters("-aaaaaaaaaaaaaaaaaaaaa>aa", |"-aaaaaaaaaaaaaaaaaaaaa>aa"|) ==> forall i :: 0 <= i < |"-aaaaaaaaaaaaaaaaaaaaa>aa"| && !IsLetter("-aaaaaaaaaaaaaaaaaaaaa>aa"[i]) ==> r0[i] == "-aaaaaaaaaaaaaaaaaaaaa>aa"[i];
expect NoLetters("-aaaaaaaaaaaaaaaaaaaaa>aa", |"-aaaaaaaaaaaaaaaaaaaaa>aa"|) ==> isReverse(r0, "-aaaaaaaaaaaaaaaaaaaaa>aa");
}
method {:test} Test8() {
var r0 := solve("pk");
expect |r0| == |"pk"|;
expect !NoLetters("pk", |"pk"|) ==> forall i :: 0 <= i < |"pk"| && IsLetter("pk"[i]) ==> r0[i] == ToggleCase("pk"[i]);
expect !NoLetters("pk", |"pk"|) ==> forall i :: 0 <= i < |"pk"| && !IsLetter("pk"[i]) ==> r0[i] == "pk"[i];
expect NoLetters("pk", |"pk"|) ==> isReverse(r0, "pk");
}

// REPEAT 3 - TIME: 77.4664541 s

method {:test} Test9() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test10() {
var r0 := solve(" a\U{000F}");
expect |r0| == |" a\U{000F}"|;
expect !NoLetters(" a\U{000F}", |" a\U{000F}"|) ==> forall i :: 0 <= i < |" a\U{000F}"| && IsLetter(" a\U{000F}"[i]) ==> r0[i] == ToggleCase(" a\U{000F}"[i]);
expect !NoLetters(" a\U{000F}", |" a\U{000F}"|) ==> forall i :: 0 <= i < |" a\U{000F}"| && !IsLetter(" a\U{000F}"[i]) ==> r0[i] == " a\U{000F}"[i];
expect NoLetters(" a\U{000F}", |" a\U{000F}"|) ==> isReverse(r0, " a\U{000F}");
}
method {:test} Test11() {
var r0 := solve("mau");
expect |r0| == |"mau"|;
expect !NoLetters("mau", |"mau"|) ==> forall i :: 0 <= i < |"mau"| && IsLetter("mau"[i]) ==> r0[i] == ToggleCase("mau"[i]);
expect !NoLetters("mau", |"mau"|) ==> forall i :: 0 <= i < |"mau"| && !IsLetter("mau"[i]) ==> r0[i] == "mau"[i];
expect NoLetters("mau", |"mau"|) ==> isReverse(r0, "mau");
}

// REPEAT 4 - TIME: 113.3915697 s

method {:test} Test12() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test13() {
var r0 := solve("-a -");
expect |r0| == |"-a -"|;
expect !NoLetters("-a -", |"-a -"|) ==> forall i :: 0 <= i < |"-a -"| && IsLetter("-a -"[i]) ==> r0[i] == ToggleCase("-a -"[i]);
expect !NoLetters("-a -", |"-a -"|) ==> forall i :: 0 <= i < |"-a -"| && !IsLetter("-a -"[i]) ==> r0[i] == "-a -"[i];
expect NoLetters("-a -", |"-a -"|) ==> isReverse(r0, "-a -");
}
method {:test} Test14() {
var r0 := solve("zaaoaaaaaaem");
expect |r0| == |"zaaoaaaaaaem"|;
expect !NoLetters("zaaoaaaaaaem", |"zaaoaaaaaaem"|) ==> forall i :: 0 <= i < |"zaaoaaaaaaem"| && IsLetter("zaaoaaaaaaem"[i]) ==> r0[i] == ToggleCase("zaaoaaaaaaem"[i]);
expect !NoLetters("zaaoaaaaaaem", |"zaaoaaaaaaem"|) ==> forall i :: 0 <= i < |"zaaoaaaaaaem"| && !IsLetter("zaaoaaaaaaem"[i]) ==> r0[i] == "zaaoaaaaaaem"[i];
expect NoLetters("zaaoaaaaaaem", |"zaaoaaaaaaem"|) ==> isReverse(r0, "zaaoaaaaaaem");
}

// REPEAT 5 - TIME: 157.3155794 s

method {:test} Test15() {
var r0 := Reverse("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> r0[i] == "aa"[|"aa"| - 1 - i];
}
method {:test} Test16() {
var r0 := solve(" a a\U{000F}");
expect |r0| == |" a a\U{000F}"|;
expect !NoLetters(" a a\U{000F}", |" a a\U{000F}"|) ==> forall i :: 0 <= i < |" a a\U{000F}"| && IsLetter(" a a\U{000F}"[i]) ==> r0[i] == ToggleCase(" a a\U{000F}"[i]);
expect !NoLetters(" a a\U{000F}", |" a a\U{000F}"|) ==> forall i :: 0 <= i < |" a a\U{000F}"| && !IsLetter(" a a\U{000F}"[i]) ==> r0[i] == " a a\U{000F}"[i];
expect NoLetters(" a a\U{000F}", |" a a\U{000F}"|) ==> isReverse(r0, " a a\U{000F}");
}
method {:test} Test17() {
var r0 := solve("paaxaaaaaaaahn");
expect |r0| == |"paaxaaaaaaaahn"|;
expect !NoLetters("paaxaaaaaaaahn", |"paaxaaaaaaaahn"|) ==> forall i :: 0 <= i < |"paaxaaaaaaaahn"| && IsLetter("paaxaaaaaaaahn"[i]) ==> r0[i] == ToggleCase("paaxaaaaaaaahn"[i]);
expect !NoLetters("paaxaaaaaaaahn", |"paaxaaaaaaaahn"|) ==> forall i :: 0 <= i < |"paaxaaaaaaaahn"| && !IsLetter("paaxaaaaaaaahn"[i]) ==> r0[i] == "paaxaaaaaaaahn"[i];
expect NoLetters("paaxaaaaaaaahn", |"paaxaaaaaaaahn"|) ==> isReverse(r0, "paaxaaaaaaaahn");
}

// REPEAT 6 - TIME: 209.1326226 s

method {:test} Test18() {
var r0 := Reverse("\0");
expect |r0| == |"\0"|;
expect forall i :: 0 <= i < |"\0"| ==> r0[i] == "\0"[|"\0"| - 1 - i];
}
method {:test} Test19() {
var r0 := solve("@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa");
expect |r0| == |"@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"|;
expect !NoLetters("@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa", |"@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"|) ==> forall i :: 0 <= i < |"@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"| && IsLetter("@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"[i]) ==> r0[i] == ToggleCase("@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"[i]);
expect !NoLetters("@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa", |"@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"|) ==> forall i :: 0 <= i < |"@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"| && !IsLetter("@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"[i]) ==> r0[i] == "@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"[i];
expect NoLetters("@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa", |"@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa"|) ==> isReverse(r0, "@a\U{0007}a7.aaaaaaaa)aaaaaa$>a\n\U{0017}aa");
}
method {:test} Test20() {
var r0 := solve("rahabaaaaaaaaaaaaaaaaya");
expect |r0| == |"rahabaaaaaaaaaaaaaaaaya"|;
expect !NoLetters("rahabaaaaaaaaaaaaaaaaya", |"rahabaaaaaaaaaaaaaaaaya"|) ==> forall i :: 0 <= i < |"rahabaaaaaaaaaaaaaaaaya"| && IsLetter("rahabaaaaaaaaaaaaaaaaya"[i]) ==> r0[i] == ToggleCase("rahabaaaaaaaaaaaaaaaaya"[i]);
expect !NoLetters("rahabaaaaaaaaaaaaaaaaya", |"rahabaaaaaaaaaaaaaaaaya"|) ==> forall i :: 0 <= i < |"rahabaaaaaaaaaaaaaaaaya"| && !IsLetter("rahabaaaaaaaaaaaaaaaaya"[i]) ==> r0[i] == "rahabaaaaaaaaaaaaaaaaya"[i];
expect NoLetters("rahabaaaaaaaaaaaaaaaaya", |"rahabaaaaaaaaaaaaaaaaya"|) ==> isReverse(r0, "rahabaaaaaaaaaaaaaaaaya");
}

// REPEAT 7 - TIME: 260.5303193 s

method {:test} Test21() {
var r0 := Reverse("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[|"\0a"| - 1 - i];
}
method {:test} Test22() {
var r0 := solve("aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$");
expect |r0| == |"aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"|;
expect !NoLetters("aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$", |"aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"|) ==> forall i :: 0 <= i < |"aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"| && IsLetter("aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"[i]) ==> r0[i] == ToggleCase("aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"[i]);
expect !NoLetters("aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$", |"aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"|) ==> forall i :: 0 <= i < |"aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"| && !IsLetter("aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"[i]) ==> r0[i] == "aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"[i];
expect NoLetters("aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$", |"aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$"|) ==> isReverse(r0, "aa\U{000E}=\U{0019}\U{0007}aaaaaaa7aaaaaaaa)a.aaa$");
}
method {:test} Test23() {
var r0 := solve("lamagpaaaaaaaaaaaavaaawafaeaae");
expect |r0| == |"lamagpaaaaaaaaaaaavaaawafaeaae"|;
expect !NoLetters("lamagpaaaaaaaaaaaavaaawafaeaae", |"lamagpaaaaaaaaaaaavaaawafaeaae"|) ==> forall i :: 0 <= i < |"lamagpaaaaaaaaaaaavaaawafaeaae"| && IsLetter("lamagpaaaaaaaaaaaavaaawafaeaae"[i]) ==> r0[i] == ToggleCase("lamagpaaaaaaaaaaaavaaawafaeaae"[i]);
expect !NoLetters("lamagpaaaaaaaaaaaavaaawafaeaae", |"lamagpaaaaaaaaaaaavaaawafaeaae"|) ==> forall i :: 0 <= i < |"lamagpaaaaaaaaaaaavaaawafaeaae"| && !IsLetter("lamagpaaaaaaaaaaaavaaawafaeaae"[i]) ==> r0[i] == "lamagpaaaaaaaaaaaavaaawafaeaae"[i];
expect NoLetters("lamagpaaaaaaaaaaaavaaawafaeaae", |"lamagpaaaaaaaaaaaavaaawafaeaae"|) ==> isReverse(r0, "lamagpaaaaaaaaaaaavaaawafaeaae");
}

// REPEAT 8 - TIME: 321.0862278 s

method {:test} Test24() {
var r0 := Reverse("\0a\U{0002}");
expect |r0| == |"\0a\U{0002}"|;
expect forall i :: 0 <= i < |"\0a\U{0002}"| ==> r0[i] == "\0a\U{0002}"[|"\0a\U{0002}"| - 1 - i];
}
method {:test} Test25() {
var r0 := solve(")a \U{0015}aaaaaa>a=");
expect |r0| == |")a \U{0015}aaaaaa>a="|;
expect !NoLetters(")a \U{0015}aaaaaa>a=", |")a \U{0015}aaaaaa>a="|) ==> forall i :: 0 <= i < |")a \U{0015}aaaaaa>a="| && IsLetter(")a \U{0015}aaaaaa>a="[i]) ==> r0[i] == ToggleCase(")a \U{0015}aaaaaa>a="[i]);
expect !NoLetters(")a \U{0015}aaaaaa>a=", |")a \U{0015}aaaaaa>a="|) ==> forall i :: 0 <= i < |")a \U{0015}aaaaaa>a="| && !IsLetter(")a \U{0015}aaaaaa>a="[i]) ==> r0[i] == ")a \U{0015}aaaaaa>a="[i];
expect NoLetters(")a \U{0015}aaaaaa>a=", |")a \U{0015}aaaaaa>a="|) ==> isReverse(r0, ")a \U{0015}aaaaaa>a=");
}
method {:test} Test26() {
var r0 := solve("xaka");
expect |r0| == |"xaka"|;
expect !NoLetters("xaka", |"xaka"|) ==> forall i :: 0 <= i < |"xaka"| && IsLetter("xaka"[i]) ==> r0[i] == ToggleCase("xaka"[i]);
expect !NoLetters("xaka", |"xaka"|) ==> forall i :: 0 <= i < |"xaka"| && !IsLetter("xaka"[i]) ==> r0[i] == "xaka"[i];
expect NoLetters("xaka", |"xaka"|) ==> isReverse(r0, "xaka");
}

// REPEAT 9 - TIME: 403.0439788 s

method {:test} Test27() {
var r0 := Reverse("\0a");
expect |r0| == |"\0a"|;
expect forall i :: 0 <= i < |"\0a"| ==> r0[i] == "\0a"[|"\0a"| - 1 - i];
}
method {:test} Test28() {
var r0 := solve("aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa");
expect |r0| == |"aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"|;
expect !NoLetters("aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa", |"aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"|) ==> forall i :: 0 <= i < |"aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"| && IsLetter("aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"[i]) ==> r0[i] == ToggleCase("aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"[i]);
expect !NoLetters("aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa", |"aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"|) ==> forall i :: 0 <= i < |"aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"| && !IsLetter("aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"[i]) ==> r0[i] == "aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"[i];
expect NoLetters("aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa", |"aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa"|) ==> isReverse(r0, "aaa=\U{0007}.aaaa\U{0019}aa)7a$a\naaaaa");
}
method {:test} Test29() {
var r0 := solve("ganaazaaaaaaaaaafaaawahaaaa");
expect |r0| == |"ganaazaaaaaaaaaafaaawahaaaa"|;
expect !NoLetters("ganaazaaaaaaaaaafaaawahaaaa", |"ganaazaaaaaaaaaafaaawahaaaa"|) ==> forall i :: 0 <= i < |"ganaazaaaaaaaaaafaaawahaaaa"| && IsLetter("ganaazaaaaaaaaaafaaawahaaaa"[i]) ==> r0[i] == ToggleCase("ganaazaaaaaaaaaafaaawahaaaa"[i]);
expect !NoLetters("ganaazaaaaaaaaaafaaawahaaaa", |"ganaazaaaaaaaaaafaaawahaaaa"|) ==> forall i :: 0 <= i < |"ganaazaaaaaaaaaafaaawahaaaa"| && !IsLetter("ganaazaaaaaaaaaafaaawahaaaa"[i]) ==> r0[i] == "ganaazaaaaaaaaaafaaawahaaaa"[i];
expect NoLetters("ganaazaaaaaaaaaafaaawahaaaa", |"ganaazaaaaaaaaaafaaawahaaaa"|) ==> isReverse(r0, "ganaazaaaaaaaaaafaaawahaaaa");
}

// REPEAT 10 - TIME: 530.8472546 s

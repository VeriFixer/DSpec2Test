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
  while true
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
var r0 := Reverse("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> r0[i] == ""[|""| - 1 - i];
}
method {:test} Test1() {
var r0 := solve("a");
expect |r0| == |"a"|;
expect !NoLetters("a", |"a"|) ==> forall i :: 0 <= i < |"a"| && IsLetter("a"[i]) ==> r0[i] == ToggleCase("a"[i]);
expect !NoLetters("a", |"a"|) ==> forall i :: 0 <= i < |"a"| && !IsLetter("a"[i]) ==> r0[i] == "a"[i];
expect NoLetters("a", |"a"|) ==> isReverse(r0, "a");
}
method {:test} Test2() {
var r0 := solve("aaaaaaaaaaaaaaaaaaaaaT");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaT"|;
expect !NoLetters("aaaaaaaaaaaaaaaaaaaaaT", |"aaaaaaaaaaaaaaaaaaaaaT"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaT"| && IsLetter("aaaaaaaaaaaaaaaaaaaaaT"[i]) ==> r0[i] == ToggleCase("aaaaaaaaaaaaaaaaaaaaaT"[i]);
expect !NoLetters("aaaaaaaaaaaaaaaaaaaaaT", |"aaaaaaaaaaaaaaaaaaaaaT"|) ==> forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaT"| && !IsLetter("aaaaaaaaaaaaaaaaaaaaaT"[i]) ==> r0[i] == "aaaaaaaaaaaaaaaaaaaaaT"[i];
expect NoLetters("aaaaaaaaaaaaaaaaaaaaaT", |"aaaaaaaaaaaaaaaaaaaaaT"|) ==> isReverse(r0, "aaaaaaaaaaaaaaaaaaaaaT");
}

// REPEAT 1 - TIME: 91.3161122 s

method {:test} Test3() {
var r0 := Reverse("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> r0[i] == "a"[|"a"| - 1 - i];
}
method {:test} Test4() {
var r0 := solve("@aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"@aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect !NoLetters("@aaaaaaaaaaaaaaaaaaaaaaaa", |"@aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"@aaaaaaaaaaaaaaaaaaaaaaaa"| && IsLetter("@aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("@aaaaaaaaaaaaaaaaaaaaaaaa"[i]);
expect !NoLetters("@aaaaaaaaaaaaaaaaaaaaaaaa", |"@aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"@aaaaaaaaaaaaaaaaaaaaaaaa"| && !IsLetter("@aaaaaaaaaaaaaaaaaaaaaaaa"[i]) ==> r0[i] == "@aaaaaaaaaaaaaaaaaaaaaaaa"[i];
expect NoLetters("@aaaaaaaaaaaaaaaaaaaaaaaa", |"@aaaaaaaaaaaaaaaaaaaaaaaa"|) ==> isReverse(r0, "@aaaaaaaaaaaaaaaaaaaaaaaa");
}
method {:test} Test5() {
var r0 := solve("aaaaaaaaYaaaaaaaaaaaaa@");
expect |r0| == |"aaaaaaaaYaaaaaaaaaaaaa@"|;
expect !NoLetters("aaaaaaaaYaaaaaaaaaaaaa@", |"aaaaaaaaYaaaaaaaaaaaaa@"|) ==> forall i :: 0 <= i < |"aaaaaaaaYaaaaaaaaaaaaa@"| && IsLetter("aaaaaaaaYaaaaaaaaaaaaa@"[i]) ==> r0[i] == ToggleCase("aaaaaaaaYaaaaaaaaaaaaa@"[i]);
expect !NoLetters("aaaaaaaaYaaaaaaaaaaaaa@", |"aaaaaaaaYaaaaaaaaaaaaa@"|) ==> forall i :: 0 <= i < |"aaaaaaaaYaaaaaaaaaaaaa@"| && !IsLetter("aaaaaaaaYaaaaaaaaaaaaa@"[i]) ==> r0[i] == "aaaaaaaaYaaaaaaaaaaaaa@"[i];
expect NoLetters("aaaaaaaaYaaaaaaaaaaaaa@", |"aaaaaaaaYaaaaaaaaaaaaa@"|) ==> isReverse(r0, "aaaaaaaaYaaaaaaaaaaaaa@");
}

// REPEAT 2 - TIME: 142.7702245 s

method {:test} Test6() {
var r0 := Reverse("a\0");
expect |r0| == |"a\0"|;
expect forall i :: 0 <= i < |"a\0"| ==> r0[i] == "a\0"[|"a\0"| - 1 - i];
}
method {:test} Test7() {
var r0 := solve("\U{000F}\U{0010}aaaaaaaa");
expect |r0| == |"\U{000F}\U{0010}aaaaaaaa"|;
expect !NoLetters("\U{000F}\U{0010}aaaaaaaa", |"\U{000F}\U{0010}aaaaaaaa"|) ==> forall i :: 0 <= i < |"\U{000F}\U{0010}aaaaaaaa"| && IsLetter("\U{000F}\U{0010}aaaaaaaa"[i]) ==> r0[i] == ToggleCase("\U{000F}\U{0010}aaaaaaaa"[i]);
expect !NoLetters("\U{000F}\U{0010}aaaaaaaa", |"\U{000F}\U{0010}aaaaaaaa"|) ==> forall i :: 0 <= i < |"\U{000F}\U{0010}aaaaaaaa"| && !IsLetter("\U{000F}\U{0010}aaaaaaaa"[i]) ==> r0[i] == "\U{000F}\U{0010}aaaaaaaa"[i];
expect NoLetters("\U{000F}\U{0010}aaaaaaaa", |"\U{000F}\U{0010}aaaaaaaa"|) ==> isReverse(r0, "\U{000F}\U{0010}aaaaaaaa");
}
method {:test} Test8() {
var r0 := solve("%\U{0003}aaaabaaaaaaaaaaaaaa");
expect |r0| == |"%\U{0003}aaaabaaaaaaaaaaaaaa"|;
expect !NoLetters("%\U{0003}aaaabaaaaaaaaaaaaaa", |"%\U{0003}aaaabaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"%\U{0003}aaaabaaaaaaaaaaaaaa"| && IsLetter("%\U{0003}aaaabaaaaaaaaaaaaaa"[i]) ==> r0[i] == ToggleCase("%\U{0003}aaaabaaaaaaaaaaaaaa"[i]);
expect !NoLetters("%\U{0003}aaaabaaaaaaaaaaaaaa", |"%\U{0003}aaaabaaaaaaaaaaaaaa"|) ==> forall i :: 0 <= i < |"%\U{0003}aaaabaaaaaaaaaaaaaa"| && !IsLetter("%\U{0003}aaaabaaaaaaaaaaaaaa"[i]) ==> r0[i] == "%\U{0003}aaaabaaaaaaaaaaaaaa"[i];
expect NoLetters("%\U{0003}aaaabaaaaaaaaaaaaaa", |"%\U{0003}aaaabaaaaaaaaaaaaaa"|) ==> isReverse(r0, "%\U{0003}aaaabaaaaaaaaaaaaaa");
}

// REPEAT 3 - TIME: 188.6874752 s

method {:test} Test9() {
var r0 := Reverse("\U{0002}\0");
expect |r0| == |"\U{0002}\0"|;
expect forall i :: 0 <= i < |"\U{0002}\0"| ==> r0[i] == "\U{0002}\0"[|"\U{0002}\0"| - 1 - i];
}
method {:test} Test10() {
var r0 := solve("");
expect |r0| == |""|;
expect !NoLetters("", |""|) ==> forall i :: 0 <= i < |""| && IsLetter(""[i]) ==> r0[i] == ToggleCase(""[i]);
expect !NoLetters("", |""|) ==> forall i :: 0 <= i < |""| && !IsLetter(""[i]) ==> r0[i] == ""[i];
expect NoLetters("", |""|) ==> isReverse(r0, "");
}
method {:test} Test11() {
var r0 := solve("9ua[YaW");
expect |r0| == |"9ua[YaW"|;
expect !NoLetters("9ua[YaW", |"9ua[YaW"|) ==> forall i :: 0 <= i < |"9ua[YaW"| && IsLetter("9ua[YaW"[i]) ==> r0[i] == ToggleCase("9ua[YaW"[i]);
expect !NoLetters("9ua[YaW", |"9ua[YaW"|) ==> forall i :: 0 <= i < |"9ua[YaW"| && !IsLetter("9ua[YaW"[i]) ==> r0[i] == "9ua[YaW"[i];
expect NoLetters("9ua[YaW", |"9ua[YaW"|) ==> isReverse(r0, "9ua[YaW");
}

// REPEAT 4 - TIME: 235.0625943 s

method {:test} Test12() {
var r0 := Reverse("\0aa");
expect |r0| == |"\0aa"|;
expect forall i :: 0 <= i < |"\0aa"| ==> r0[i] == "\0aa"[|"\0aa"| - 1 - i];
}
method {:test} Test13() {
var r0 := solve("-aa");
expect |r0| == |"-aa"|;
expect !NoLetters("-aa", |"-aa"|) ==> forall i :: 0 <= i < |"-aa"| && IsLetter("-aa"[i]) ==> r0[i] == ToggleCase("-aa"[i]);
expect !NoLetters("-aa", |"-aa"|) ==> forall i :: 0 <= i < |"-aa"| && !IsLetter("-aa"[i]) ==> r0[i] == "-aa"[i];
expect NoLetters("-aa", |"-aa"|) ==> isReverse(r0, "-aa");
}
method {:test} Test14() {
var r0 := solve(">OaxaaaV");
expect |r0| == |">OaxaaaV"|;
expect !NoLetters(">OaxaaaV", |">OaxaaaV"|) ==> forall i :: 0 <= i < |">OaxaaaV"| && IsLetter(">OaxaaaV"[i]) ==> r0[i] == ToggleCase(">OaxaaaV"[i]);
expect !NoLetters(">OaxaaaV", |">OaxaaaV"|) ==> forall i :: 0 <= i < |">OaxaaaV"| && !IsLetter(">OaxaaaV"[i]) ==> r0[i] == ">OaxaaaV"[i];
expect NoLetters(">OaxaaaV", |">OaxaaaV"|) ==> isReverse(r0, ">OaxaaaV");
}

// REPEAT 5 - TIME: 281.6850117 s

method {:test} Test15() {
var r0 := Reverse("a\0aa");
expect |r0| == |"a\0aa"|;
expect forall i :: 0 <= i < |"a\0aa"| ==> r0[i] == "a\0aa"[|"a\0aa"| - 1 - i];
}
method {:test} Test16() {
var r0 := solve(";\U{000F}");
expect |r0| == |";\U{000F}"|;
expect !NoLetters(";\U{000F}", |";\U{000F}"|) ==> forall i :: 0 <= i < |";\U{000F}"| && IsLetter(";\U{000F}"[i]) ==> r0[i] == ToggleCase(";\U{000F}"[i]);
expect !NoLetters(";\U{000F}", |";\U{000F}"|) ==> forall i :: 0 <= i < |";\U{000F}"| && !IsLetter(";\U{000F}"[i]) ==> r0[i] == ";\U{000F}"[i];
expect NoLetters(";\U{000F}", |";\U{000F}"|) ==> isReverse(r0, ";\U{000F}");
}
method {:test} Test17() {
var r0 := solve("\U{001C}_ka");
expect |r0| == |"\U{001C}_ka"|;
expect !NoLetters("\U{001C}_ka", |"\U{001C}_ka"|) ==> forall i :: 0 <= i < |"\U{001C}_ka"| && IsLetter("\U{001C}_ka"[i]) ==> r0[i] == ToggleCase("\U{001C}_ka"[i]);
expect !NoLetters("\U{001C}_ka", |"\U{001C}_ka"|) ==> forall i :: 0 <= i < |"\U{001C}_ka"| && !IsLetter("\U{001C}_ka"[i]) ==> r0[i] == "\U{001C}_ka"[i];
expect NoLetters("\U{001C}_ka", |"\U{001C}_ka"|) ==> isReverse(r0, "\U{001C}_ka");
}

// REPEAT 6 - TIME: 328.2665373 s

method {:test} Test18() {
var r0 := Reverse("\U{0004}\U{0002}aaaaaaaaaaaaaaaaa\0");
expect |r0| == |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |"\U{0004}\U{0002}aaaaaaaaaaaaaaaaa\0"| ==> r0[i] == "\U{0004}\U{0002}aaaaaaaaaaaaaaaaa\0"[|"\U{0004}\U{0002}aaaaaaaaaaaaaaaaa\0"| - 1 - i];
}
method {:test} Test19() {
var r0 := solve("\U{0003}\U{0010} \U{000F} ");
expect |r0| == |"\U{0003}\U{0010} \U{000F} "|;
expect !NoLetters("\U{0003}\U{0010} \U{000F} ", |"\U{0003}\U{0010} \U{000F} "|) ==> forall i :: 0 <= i < |"\U{0003}\U{0010} \U{000F} "| && IsLetter("\U{0003}\U{0010} \U{000F} "[i]) ==> r0[i] == ToggleCase("\U{0003}\U{0010} \U{000F} "[i]);
expect !NoLetters("\U{0003}\U{0010} \U{000F} ", |"\U{0003}\U{0010} \U{000F} "|) ==> forall i :: 0 <= i < |"\U{0003}\U{0010} \U{000F} "| && !IsLetter("\U{0003}\U{0010} \U{000F} "[i]) ==> r0[i] == "\U{0003}\U{0010} \U{000F} "[i];
expect NoLetters("\U{0003}\U{0010} \U{000F} ", |"\U{0003}\U{0010} \U{000F} "|) ==> isReverse(r0, "\U{0003}\U{0010} \U{000F} ");
}
method {:test} Test20() {
var r0 := solve("\U{0019}S-q");
expect |r0| == |"\U{0019}S-q"|;
expect !NoLetters("\U{0019}S-q", |"\U{0019}S-q"|) ==> forall i :: 0 <= i < |"\U{0019}S-q"| && IsLetter("\U{0019}S-q"[i]) ==> r0[i] == ToggleCase("\U{0019}S-q"[i]);
expect !NoLetters("\U{0019}S-q", |"\U{0019}S-q"|) ==> forall i :: 0 <= i < |"\U{0019}S-q"| && !IsLetter("\U{0019}S-q"[i]) ==> r0[i] == "\U{0019}S-q"[i];
expect NoLetters("\U{0019}S-q", |"\U{0019}S-q"|) ==> isReverse(r0, "\U{0019}S-q");
}

// REPEAT 7 - TIME: 377.2185433 s

method {:test} Test21() {
var r0 := Reverse("a\0aaaaaaaaaaa\U{0002}");
expect |r0| == |"a\0aaaaaaaaaaa\U{0002}"|;
expect forall i :: 0 <= i < |"a\0aaaaaaaaaaa\U{0002}"| ==> r0[i] == "a\0aaaaaaaaaaa\U{0002}"[|"a\0aaaaaaaaaaa\U{0002}"| - 1 - i];
}
method {:test} Test22() {
var r0 := solve("& aa-2a>\U{0003}");
expect |r0| == |"& aa-2a>\U{0003}"|;
expect !NoLetters("& aa-2a>\U{0003}", |"& aa-2a>\U{0003}"|) ==> forall i :: 0 <= i < |"& aa-2a>\U{0003}"| && IsLetter("& aa-2a>\U{0003}"[i]) ==> r0[i] == ToggleCase("& aa-2a>\U{0003}"[i]);
expect !NoLetters("& aa-2a>\U{0003}", |"& aa-2a>\U{0003}"|) ==> forall i :: 0 <= i < |"& aa-2a>\U{0003}"| && !IsLetter("& aa-2a>\U{0003}"[i]) ==> r0[i] == "& aa-2a>\U{0003}"[i];
expect NoLetters("& aa-2a>\U{0003}", |"& aa-2a>\U{0003}"|) ==> isReverse(r0, "& aa-2a>\U{0003}");
}
method {:test} Test23() {
var r0 := solve("WZ]saaaaYZa");
expect |r0| == |"WZ]saaaaYZa"|;
expect !NoLetters("WZ]saaaaYZa", |"WZ]saaaaYZa"|) ==> forall i :: 0 <= i < |"WZ]saaaaYZa"| && IsLetter("WZ]saaaaYZa"[i]) ==> r0[i] == ToggleCase("WZ]saaaaYZa"[i]);
expect !NoLetters("WZ]saaaaYZa", |"WZ]saaaaYZa"|) ==> forall i :: 0 <= i < |"WZ]saaaaYZa"| && !IsLetter("WZ]saaaaYZa"[i]) ==> r0[i] == "WZ]saaaaYZa"[i];
expect NoLetters("WZ]saaaaYZa", |"WZ]saaaaYZa"|) ==> isReverse(r0, "WZ]saaaaYZa");
}

// REPEAT 8 - TIME: 425.2022309 s

method {:test} Test24() {
var r0 := Reverse("\U{0002}\0aaaaaaaaaa\U{0004}");
expect |r0| == |"\U{0002}\0aaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0002}\0aaaaaaaaaa\U{0004}"| ==> r0[i] == "\U{0002}\0aaaaaaaaaa\U{0004}"[|"\U{0002}\0aaaaaaaaaa\U{0004}"| - 1 - i];
}
method {:test} Test25() {
var r0 := solve(">\U{000F}0a");
expect |r0| == |">\U{000F}0a"|;
expect !NoLetters(">\U{000F}0a", |">\U{000F}0a"|) ==> forall i :: 0 <= i < |">\U{000F}0a"| && IsLetter(">\U{000F}0a"[i]) ==> r0[i] == ToggleCase(">\U{000F}0a"[i]);
expect !NoLetters(">\U{000F}0a", |">\U{000F}0a"|) ==> forall i :: 0 <= i < |">\U{000F}0a"| && !IsLetter(">\U{000F}0a"[i]) ==> r0[i] == ">\U{000F}0a"[i];
expect NoLetters(">\U{000F}0a", |">\U{000F}0a"|) ==> isReverse(r0, ">\U{000F}0a");
}
method {:test} Test26() {
var r0 := solve("\'\U{001F}8aj@&");
expect |r0| == |"\'\U{001F}8aj@&"|;
expect !NoLetters("\'\U{001F}8aj@&", |"\'\U{001F}8aj@&"|) ==> forall i :: 0 <= i < |"\'\U{001F}8aj@&"| && IsLetter("\'\U{001F}8aj@&"[i]) ==> r0[i] == ToggleCase("\'\U{001F}8aj@&"[i]);
expect !NoLetters("\'\U{001F}8aj@&", |"\'\U{001F}8aj@&"|) ==> forall i :: 0 <= i < |"\'\U{001F}8aj@&"| && !IsLetter("\'\U{001F}8aj@&"[i]) ==> r0[i] == "\'\U{001F}8aj@&"[i];
expect NoLetters("\'\U{001F}8aj@&", |"\'\U{001F}8aj@&"|) ==> isReverse(r0, "\'\U{001F}8aj@&");
}

// REPEAT 9 - TIME: 473.1968572 s

method {:test} Test27() {
var r0 := Reverse("\U{0002}\0a");
expect |r0| == |"\U{0002}\0a"|;
expect forall i :: 0 <= i < |"\U{0002}\0a"| ==> r0[i] == "\U{0002}\0a"[|"\U{0002}\0a"| - 1 - i];
}
method {:test} Test28() {
var r0 := solve("aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2");
expect |r0| == |"aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"|;
expect !NoLetters("aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2", |"aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"|) ==> forall i :: 0 <= i < |"aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"| && IsLetter("aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"[i]) ==> r0[i] == ToggleCase("aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"[i]);
expect !NoLetters("aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2", |"aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"|) ==> forall i :: 0 <= i < |"aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"| && !IsLetter("aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"[i]) ==> r0[i] == "aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"[i];
expect NoLetters("aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2", |"aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2"|) ==> isReverse(r0, "aaaa0aaa \U{000F} aaaaaaaaa\U{000F}--2");
}
method {:test} Test29() {
var r0 := solve("NMnaaD");
expect |r0| == |"NMnaaD"|;
expect !NoLetters("NMnaaD", |"NMnaaD"|) ==> forall i :: 0 <= i < |"NMnaaD"| && IsLetter("NMnaaD"[i]) ==> r0[i] == ToggleCase("NMnaaD"[i]);
expect !NoLetters("NMnaaD", |"NMnaaD"|) ==> forall i :: 0 <= i < |"NMnaaD"| && !IsLetter("NMnaaD"[i]) ==> r0[i] == "NMnaaD"[i];
expect NoLetters("NMnaaD", |"NMnaaD"|) ==> isReverse(r0, "NMnaaD");
}

// REPEAT 10 - TIME: 521.2687359 s

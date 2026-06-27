// dafny-synthesis_task_id_557.dfy

predicate IsLowerCase(c: char)
{
  97 <= c as int <= 122
}

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

predicate IsLowerUpperPair(c: char, C: char)
{
  c as int == C as int + 32
}

predicate IsUpperLowerPair(C: char, c: char)
{
  C as int == c as int - 32
}

function ShiftMinus32(c: char): char
{
  ((c as int - 32) % 128) as char
}

function Shift32(c: char): char
{
  ((c as int + 32) % 128) as char
}

method {:testEntry} ToggleCase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) && !IsUpperCase(s[k]) ==> s[k] == s'[k]
  {
    if IsLowerCase(s[i]) {
    } else if IsUpperCase(s[i]) {
      s' := s' + [Shift32(s[i])];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ToggleCase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test5() {
var r0 := ToggleCase("a`");
expect |r0| == |"a`"|;
expect forall i :: 0 <= i < |"a`"| ==> if IsLowerCase("a`"[i]) then IsLowerUpperPair("a`"[i], r0[i]) else if IsUpperCase("a`"[i]) then IsUpperLowerPair("a`"[i], r0[i]) else r0[i] == "a`"[i];
}

// REPEAT 1 - TIME: 6.1481375 s

method {:test} Test6() {
var r0 := ToggleCase("aa@");
expect |r0| == |"aa@"|;
expect forall i :: 0 <= i < |"aa@"| ==> if IsLowerCase("aa@"[i]) then IsLowerUpperPair("aa@"[i], r0[i]) else if IsUpperCase("aa@"[i]) then IsUpperLowerPair("aa@"[i], r0[i]) else r0[i] == "aa@"[i];
}
method {:test} Test7() {
var r0 := ToggleCase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test8() {
var r0 := ToggleCase("afc");
expect |r0| == |"afc"|;
expect forall i :: 0 <= i < |"afc"| ==> if IsLowerCase("afc"[i]) then IsLowerUpperPair("afc"[i], r0[i]) else if IsUpperCase("afc"[i]) then IsUpperLowerPair("afc"[i], r0[i]) else r0[i] == "afc"[i];
}
method {:test} Test9() {
var r0 := ToggleCase("a\U{000F} ");
expect |r0| == |"a\U{000F} "|;
expect forall i :: 0 <= i < |"a\U{000F} "| ==> if IsLowerCase("a\U{000F} "[i]) then IsLowerUpperPair("a\U{000F} "[i], r0[i]) else if IsUpperCase("a\U{000F} "[i]) then IsUpperLowerPair("a\U{000F} "[i], r0[i]) else r0[i] == "a\U{000F} "[i];
}
method {:test} Test10() {
var r0 := ToggleCase("k");
expect |r0| == |"k"|;
expect forall i :: 0 <= i < |"k"| ==> if IsLowerCase("k"[i]) then IsLowerUpperPair("k"[i], r0[i]) else if IsUpperCase("k"[i]) then IsUpperLowerPair("k"[i], r0[i]) else r0[i] == "k"[i];
}
method {:test} Test11() {
var r0 := ToggleCase("C{");
expect |r0| == |"C{"|;
expect forall i :: 0 <= i < |"C{"| ==> if IsLowerCase("C{"[i]) then IsLowerUpperPair("C{"[i], r0[i]) else if IsUpperCase("C{"[i]) then IsUpperLowerPair("C{"[i], r0[i]) else r0[i] == "C{"[i];
}

// REPEAT 2 - TIME: 9.5108206 s

method {:test} Test12() {
var r0 := ToggleCase("paaaaaaaaaaaaaaaaaaaaaajasaayq");
expect |r0| == |"paaaaaaaaaaaaaaaaaaaaaajasaayq"|;
expect forall i :: 0 <= i < |"paaaaaaaaaaaaaaaaaaaaaajasaayq"| ==> if IsLowerCase("paaaaaaaaaaaaaaaaaaaaaajasaayq"[i]) then IsLowerUpperPair("paaaaaaaaaaaaaaaaaaaaaajasaayq"[i], r0[i]) else if IsUpperCase("paaaaaaaaaaaaaaaaaaaaaajasaayq"[i]) then IsUpperLowerPair("paaaaaaaaaaaaaaaaaaaaaajasaayq"[i], r0[i]) else r0[i] == "paaaaaaaaaaaaaaaaaaaaaajasaayq"[i];
}
method {:test} Test13() {
var r0 := ToggleCase("=C\U{0015}a");
expect |r0| == |"=C\U{0015}a"|;
expect forall i :: 0 <= i < |"=C\U{0015}a"| ==> if IsLowerCase("=C\U{0015}a"[i]) then IsLowerUpperPair("=C\U{0015}a"[i], r0[i]) else if IsUpperCase("=C\U{0015}a"[i]) then IsUpperLowerPair("=C\U{0015}a"[i], r0[i]) else r0[i] == "=C\U{0015}a"[i];
}
method {:test} Test14() {
var r0 := ToggleCase("\U{000C}m");
expect |r0| == |"\U{000C}m"|;
expect forall i :: 0 <= i < |"\U{000C}m"| ==> if IsLowerCase("\U{000C}m"[i]) then IsLowerUpperPair("\U{000C}m"[i], r0[i]) else if IsUpperCase("\U{000C}m"[i]) then IsUpperLowerPair("\U{000C}m"[i], r0[i]) else r0[i] == "\U{000C}m"[i];
}
method {:test} Test15() {
var r0 := ToggleCase("\U{0010}aaa");
expect |r0| == |"\U{0010}aaa"|;
expect forall i :: 0 <= i < |"\U{0010}aaa"| ==> if IsLowerCase("\U{0010}aaa"[i]) then IsLowerUpperPair("\U{0010}aaa"[i], r0[i]) else if IsUpperCase("\U{0010}aaa"[i]) then IsUpperLowerPair("\U{0010}aaa"[i], r0[i]) else r0[i] == "\U{0010}aaa"[i];
}
method {:test} Test16() {
var r0 := ToggleCase("wraa");
expect |r0| == |"wraa"|;
expect forall i :: 0 <= i < |"wraa"| ==> if IsLowerCase("wraa"[i]) then IsLowerUpperPair("wraa"[i], r0[i]) else if IsUpperCase("wraa"[i]) then IsUpperLowerPair("wraa"[i], r0[i]) else r0[i] == "wraa"[i];
}
method {:test} Test17() {
var r0 := ToggleCase("sa(aaaaaaaaaayaaaaaa\U{001A}aaaaaaaa");
expect |r0| == |"sa(aaaaaaaaaayaaaaaa\U{001A}aaaaaaaa"|;
expect forall i :: 0 <= i < |"sa(aaaaaaaaaayaaaaaa\U{001A}aaaaaaaa"| ==> if IsLowerCase("sa(aaaaaaaaaayaaaaaa\U{001A}aaaaaaaa"[i]) then IsLowerUpperPair("sa(aaaaaaaaaayaaaaaa\U{001A}aaaaaaaa"[i], r0[i]) else if IsUpperCase("sa(aaaaaaaaaayaaaaaa\U{001A}aaaaaaaa"[i]) then IsUpperLowerPair("sa(aaaaaaaaaayaaaaaa\U{001A}aaaaaaaa"[i], r0[i]) else r0[i] == "sa(aaaaaaaaaayaaaaaa\U{001A}aaaaaaaa"[i];
}

// REPEAT 3 - TIME: 12.2611767 s

method {:test} Test18() {
var r0 := ToggleCase("eaaapaaaaaaaaaaafaaaaaaaaaagab");
expect |r0| == |"eaaapaaaaaaaaaaafaaaaaaaaaagab"|;
expect forall i :: 0 <= i < |"eaaapaaaaaaaaaaafaaaaaaaaaagab"| ==> if IsLowerCase("eaaapaaaaaaaaaaafaaaaaaaaaagab"[i]) then IsLowerUpperPair("eaaapaaaaaaaaaaafaaaaaaaaaagab"[i], r0[i]) else if IsUpperCase("eaaapaaaaaaaaaaafaaaaaaaaaagab"[i]) then IsUpperLowerPair("eaaapaaaaaaaaaaafaaaaaaaaaagab"[i], r0[i]) else r0[i] == "eaaapaaaaaaaaaaafaaaaaaaaaagab"[i];
}
method {:test} Test19() {
var r0 := ToggleCase("\U{0002}a-aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0002}a-aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0002}a-aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0002}a-aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0002}a-aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{0002}a-aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0002}a-aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0002}a-aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test20() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaacaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaacaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaacaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaacaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaacaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaacaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaacaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaacaa"[i];
}
method {:test} Test21() {
var r0 := ToggleCase("\U{000F}a0aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{000F}a0aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{000F}a0aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{000F}a0aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{000F}a0aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("\U{000F}a0aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{000F}a0aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{000F}a0aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test22() {
var r0 := ToggleCase("yaaaa");
expect |r0| == |"yaaaa"|;
expect forall i :: 0 <= i < |"yaaaa"| ==> if IsLowerCase("yaaaa"[i]) then IsLowerUpperPair("yaaaa"[i], r0[i]) else if IsUpperCase("yaaaa"[i]) then IsUpperLowerPair("yaaaa"[i], r0[i]) else r0[i] == "yaaaa"[i];
}
method {:test} Test23() {
var r0 := ToggleCase("\U{0004}a\U{0001}\U{0003}gaaaaaaaaaaaaa\U{0005}aaaaaaa\U{0008}aa");
expect |r0| == |"\U{0004}a\U{0001}\U{0003}gaaaaaaaaaaaaa\U{0005}aaaaaaa\U{0008}aa"|;
expect forall i :: 0 <= i < |"\U{0004}a\U{0001}\U{0003}gaaaaaaaaaaaaa\U{0005}aaaaaaa\U{0008}aa"| ==> if IsLowerCase("\U{0004}a\U{0001}\U{0003}gaaaaaaaaaaaaa\U{0005}aaaaaaa\U{0008}aa"[i]) then IsLowerUpperPair("\U{0004}a\U{0001}\U{0003}gaaaaaaaaaaaaa\U{0005}aaaaaaa\U{0008}aa"[i], r0[i]) else if IsUpperCase("\U{0004}a\U{0001}\U{0003}gaaaaaaaaaaaaa\U{0005}aaaaaaa\U{0008}aa"[i]) then IsUpperLowerPair("\U{0004}a\U{0001}\U{0003}gaaaaaaaaaaaaa\U{0005}aaaaaaa\U{0008}aa"[i], r0[i]) else r0[i] == "\U{0004}a\U{0001}\U{0003}gaaaaaaaaaaaaa\U{0005}aaaaaaa\U{0008}aa"[i];
}

// REPEAT 4 - TIME: 15.7559669 s

method {:test} Test24() {
var r0 := ToggleCase("caaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"caaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"caaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("caaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("caaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("caaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("caaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "caaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test25() {
var r0 := ToggleCase("y\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"y\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"y\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("y\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("y\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("y\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("y\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "y\U{0003}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test26() {
var r0 := ToggleCase("va");
expect |r0| == |"va"|;
expect forall i :: 0 <= i < |"va"| ==> if IsLowerCase("va"[i]) then IsLowerUpperPair("va"[i], r0[i]) else if IsUpperCase("va"[i]) then IsUpperLowerPair("va"[i], r0[i]) else r0[i] == "va"[i];
}
method {:test} Test27() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test28() {
var r0 := ToggleCase("\U{0015}a");
expect |r0| == |"\U{0015}a"|;
expect forall i :: 0 <= i < |"\U{0015}a"| ==> if IsLowerCase("\U{0015}a"[i]) then IsLowerUpperPair("\U{0015}a"[i], r0[i]) else if IsUpperCase("\U{0015}a"[i]) then IsUpperLowerPair("\U{0015}a"[i], r0[i]) else r0[i] == "\U{0015}a"[i];
}
method {:test} Test29() {
var r0 := ToggleCase("aaaaDaaaaaaaaaaaa\0aaaaaaaaaa");
expect |r0| == |"aaaaDaaaaaaaaaaaa\0aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaDaaaaaaaaaaaa\0aaaaaaaaaa"| ==> if IsLowerCase("aaaaDaaaaaaaaaaaa\0aaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaDaaaaaaaaaaaa\0aaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaDaaaaaaaaaaaa\0aaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaDaaaaaaaaaaaa\0aaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaDaaaaaaaaaaaa\0aaaaaaaaaa"[i];
}

// REPEAT 5 - TIME: 19.3986092 s

method {:test} Test30() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToggleCase("0a");
expect |r0| == |"0a"|;
expect forall i :: 0 <= i < |"0a"| ==> if IsLowerCase("0a"[i]) then IsLowerUpperPair("0a"[i], r0[i]) else if IsUpperCase("0a"[i]) then IsUpperLowerPair("0a"[i], r0[i]) else r0[i] == "0a"[i];
}
method {:test} Test33() {
var r0 := ToggleCase(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair(" aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == " aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToggleCase("aaaaaaaaaaaaaaTaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaTaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaTaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaTaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaTaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaTaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaTaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaTaaaaaaaaaaa"[i];
}

// REPEAT 6 - TIME: 23.2557952 s

method {:test} Test36() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test37() {
var r0 := ToggleCase("8a");
expect |r0| == |"8a"|;
expect forall i :: 0 <= i < |"8a"| ==> if IsLowerCase("8a"[i]) then IsLowerUpperPair("8a"[i], r0[i]) else if IsUpperCase("8a"[i]) then IsUpperLowerPair("8a"[i], r0[i]) else r0[i] == "8a"[i];
}
method {:test} Test38() {
var r0 := ToggleCase("\na");
expect |r0| == |"\na"|;
expect forall i :: 0 <= i < |"\na"| ==> if IsLowerCase("\na"[i]) then IsLowerUpperPair("\na"[i], r0[i]) else if IsUpperCase("\na"[i]) then IsUpperLowerPair("\na"[i], r0[i]) else r0[i] == "\na"[i];
}
method {:test} Test39() {
var r0 := ToggleCase("Da");
expect |r0| == |"Da"|;
expect forall i :: 0 <= i < |"Da"| ==> if IsLowerCase("Da"[i]) then IsLowerUpperPair("Da"[i], r0[i]) else if IsUpperCase("Da"[i]) then IsUpperLowerPair("Da"[i], r0[i]) else r0[i] == "Da"[i];
}
method {:test} Test40() {
var r0 := ToggleCase("=a");
expect |r0| == |"=a"|;
expect forall i :: 0 <= i < |"=a"| ==> if IsLowerCase("=a"[i]) then IsLowerUpperPair("=a"[i], r0[i]) else if IsUpperCase("=a"[i]) then IsUpperLowerPair("=a"[i], r0[i]) else r0[i] == "=a"[i];
}
method {:test} Test41() {
var r0 := ToggleCase("aaaaaaaaaaaaaaa\U{0004}aaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaa\U{0004}aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaa\U{0004}aaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaa\U{0004}aaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaa\U{0004}aaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaa\U{0004}aaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaa\U{0004}aaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaa\U{0004}aaaaaaaa"[i];
}

// REPEAT 7 - TIME: 27.30586 s

method {:test} Test42() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test43() {
var r0 := ToggleCase("9a");
expect |r0| == |"9a"|;
expect forall i :: 0 <= i < |"9a"| ==> if IsLowerCase("9a"[i]) then IsLowerUpperPair("9a"[i], r0[i]) else if IsUpperCase("9a"[i]) then IsUpperLowerPair("9a"[i], r0[i]) else r0[i] == "9a"[i];
}
method {:test} Test44() {
var r0 := ToggleCase("$a");
expect |r0| == |"$a"|;
expect forall i :: 0 <= i < |"$a"| ==> if IsLowerCase("$a"[i]) then IsLowerUpperPair("$a"[i], r0[i]) else if IsUpperCase("$a"[i]) then IsUpperLowerPair("$a"[i], r0[i]) else r0[i] == "$a"[i];
}
method {:test} Test45() {
var r0 := ToggleCase("Pa");
expect |r0| == |"Pa"|;
expect forall i :: 0 <= i < |"Pa"| ==> if IsLowerCase("Pa"[i]) then IsLowerUpperPair("Pa"[i], r0[i]) else if IsUpperCase("Pa"[i]) then IsUpperLowerPair("Pa"[i], r0[i]) else r0[i] == "Pa"[i];
}
method {:test} Test46() {
var r0 := ToggleCase("\U{0014}a");
expect |r0| == |"\U{0014}a"|;
expect forall i :: 0 <= i < |"\U{0014}a"| ==> if IsLowerCase("\U{0014}a"[i]) then IsLowerUpperPair("\U{0014}a"[i], r0[i]) else if IsUpperCase("\U{0014}a"[i]) then IsUpperLowerPair("\U{0014}a"[i], r0[i]) else r0[i] == "\U{0014}a"[i];
}
method {:test} Test47() {
var r0 := ToggleCase("aaaaaaaaaTaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaTaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaTaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaTaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaTaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaTaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaTaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaTaaaaaaaaaaaaa"[i];
}

// REPEAT 8 - TIME: 31.3623563 s

method {:test} Test48() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test49() {
var r0 := ToggleCase(">a");
expect |r0| == |">a"|;
expect forall i :: 0 <= i < |">a"| ==> if IsLowerCase(">a"[i]) then IsLowerUpperPair(">a"[i], r0[i]) else if IsUpperCase(">a"[i]) then IsUpperLowerPair(">a"[i], r0[i]) else r0[i] == ">a"[i];
}
method {:test} Test50() {
var r0 := ToggleCase("%a");
expect |r0| == |"%a"|;
expect forall i :: 0 <= i < |"%a"| ==> if IsLowerCase("%a"[i]) then IsLowerUpperPair("%a"[i], r0[i]) else if IsUpperCase("%a"[i]) then IsUpperLowerPair("%a"[i], r0[i]) else r0[i] == "%a"[i];
}
method {:test} Test51() {
var r0 := ToggleCase("Na");
expect |r0| == |"Na"|;
expect forall i :: 0 <= i < |"Na"| ==> if IsLowerCase("Na"[i]) then IsLowerUpperPair("Na"[i], r0[i]) else if IsUpperCase("Na"[i]) then IsUpperLowerPair("Na"[i], r0[i]) else r0[i] == "Na"[i];
}
method {:test} Test52() {
var r0 := ToggleCase("-a");
expect |r0| == |"-a"|;
expect forall i :: 0 <= i < |"-a"| ==> if IsLowerCase("-a"[i]) then IsLowerUpperPair("-a"[i], r0[i]) else if IsUpperCase("-a"[i]) then IsUpperLowerPair("-a"[i], r0[i]) else r0[i] == "-a"[i];
}
method {:test} Test53() {
var r0 := ToggleCase(":aaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |":aaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |":aaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase(":aaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair(":aaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase(":aaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair(":aaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == ":aaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 9 - TIME: 36.0211705 s

method {:test} Test54() {
var r0 := ToggleCase("aaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase("aaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test55() {
var r0 := ToggleCase("[a");
expect |r0| == |"[a"|;
expect forall i :: 0 <= i < |"[a"| ==> if IsLowerCase("[a"[i]) then IsLowerUpperPair("[a"[i], r0[i]) else if IsUpperCase("[a"[i]) then IsUpperLowerPair("[a"[i], r0[i]) else r0[i] == "[a"[i];
}
method {:test} Test56() {
var r0 := ToggleCase("\U{C0EF}a");
expect |r0| == |"\U{C0EF}a"|;
expect forall i :: 0 <= i < |"\U{C0EF}a"| ==> if IsLowerCase("\U{C0EF}a"[i]) then IsLowerUpperPair("\U{C0EF}a"[i], r0[i]) else if IsUpperCase("\U{C0EF}a"[i]) then IsUpperLowerPair("\U{C0EF}a"[i], r0[i]) else r0[i] == "\U{C0EF}a"[i];
}
method {:test} Test57() {
var r0 := ToggleCase("Wa");
expect |r0| == |"Wa"|;
expect forall i :: 0 <= i < |"Wa"| ==> if IsLowerCase("Wa"[i]) then IsLowerUpperPair("Wa"[i], r0[i]) else if IsUpperCase("Wa"[i]) then IsUpperLowerPair("Wa"[i], r0[i]) else r0[i] == "Wa"[i];
}
method {:test} Test58() {
var r0 := ToggleCase("@a");
expect |r0| == |"@a"|;
expect forall i :: 0 <= i < |"@a"| ==> if IsLowerCase("@a"[i]) then IsLowerUpperPair("@a"[i], r0[i]) else if IsUpperCase("@a"[i]) then IsUpperLowerPair("@a"[i], r0[i]) else r0[i] == "@a"[i];
}
method {:test} Test59() {
var r0 := ToggleCase(":aaaaaaaaaaaaaaaaaaaa");
expect |r0| == |":aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |":aaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase(":aaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair(":aaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else if IsUpperCase(":aaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair(":aaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == ":aaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 10 - TIME: 40.8595745 s

// dafny-synthesis_task_id_624.dfy

predicate IsLowerCase(c: char)
{
  97 <= c as int <= 122
}

predicate IsLowerUpperPair(c: char, C: char)
{
  c as int == C as int + 32
}

function ShiftMinus32(c: char): char
{
  ((c as int - 32) % 128) as char
}

method {:testEntry} ToUppercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
  var s': string := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) ==> s[k] == s'[k]
  {
    if IsLowerCase(s[i]) {
      s' := s';
    } else {
      s' := s';
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ToUppercase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test2() {
var r0 := ToUppercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test3() {
var r0 := ToUppercase("a`");
expect |r0| == |"a`"|;
expect forall i :: 0 <= i < |"a`"| ==> if IsLowerCase("a`"[i]) then IsLowerUpperPair("a`"[i], r0[i]) else r0[i] == "a`"[i];
}

// REPEAT 1 - TIME: 3.9203147 s

method {:test} Test4() {
var r0 := ToUppercase("n");
expect |r0| == |"n"|;
expect forall i :: 0 <= i < |"n"| ==> if IsLowerCase("n"[i]) then IsLowerUpperPair("n"[i], r0[i]) else r0[i] == "n"[i];
}
method {:test} Test5() {
var r0 := ToUppercase("{");
expect |r0| == |"{"|;
expect forall i :: 0 <= i < |"{"| ==> if IsLowerCase("{"[i]) then IsLowerUpperPair("{"[i], r0[i]) else r0[i] == "{"[i];
}
method {:test} Test6() {
var r0 := ToUppercase("F");
expect |r0| == |"F"|;
expect forall i :: 0 <= i < |"F"| ==> if IsLowerCase("F"[i]) then IsLowerUpperPair("F"[i], r0[i]) else r0[i] == "F"[i];
}
method {:test} Test7() {
var r0 := ToUppercase(":cd");
expect |r0| == |":cd"|;
expect forall i :: 0 <= i < |":cd"| ==> if IsLowerCase(":cd"[i]) then IsLowerUpperPair(":cd"[i], r0[i]) else r0[i] == ":cd"[i];
}

// REPEAT 2 - TIME: 6.8382755 s

method {:test} Test8() {
var r0 := ToUppercase("\U{0004}a8");
expect |r0| == |"\U{0004}a8"|;
expect forall i :: 0 <= i < |"\U{0004}a8"| ==> if IsLowerCase("\U{0004}a8"[i]) then IsLowerUpperPair("\U{0004}a8"[i], r0[i]) else r0[i] == "\U{0004}a8"[i];
}
method {:test} Test9() {
var r0 := ToUppercase("9Q\U{2128}");
expect |r0| == |"9Q\U{2128}"|;
expect forall i :: 0 <= i < |"9Q\U{2128}"| ==> if IsLowerCase("9Q\U{2128}"[i]) then IsLowerUpperPair("9Q\U{2128}"[i], r0[i]) else r0[i] == "9Q\U{2128}"[i];
}
method {:test} Test10() {
var r0 := ToUppercase("Haaaaaaaaaaa\U{001B}aaaaaaaaaaaaaaa\U{178B}");
expect |r0| == |"Haaaaaaaaaaa\U{001B}aaaaaaaaaaaaaaa\U{178B}"|;
expect forall i :: 0 <= i < |"Haaaaaaaaaaa\U{001B}aaaaaaaaaaaaaaa\U{178B}"| ==> if IsLowerCase("Haaaaaaaaaaa\U{001B}aaaaaaaaaaaaaaa\U{178B}"[i]) then IsLowerUpperPair("Haaaaaaaaaaa\U{001B}aaaaaaaaaaaaaaa\U{178B}"[i], r0[i]) else r0[i] == "Haaaaaaaaaaa\U{001B}aaaaaaaaaaaaaaa\U{178B}"[i];
}
method {:test} Test11() {
var r0 := ToUppercase("a(a");
expect |r0| == |"a(a"|;
expect forall i :: 0 <= i < |"a(a"| ==> if IsLowerCase("a(a"[i]) then IsLowerUpperPair("a(a"[i], r0[i]) else r0[i] == "a(a"[i];
}

// REPEAT 3 - TIME: 9.4571065 s

method {:test} Test12() {
var r0 := ToUppercase("Da8\\");
expect |r0| == |"Da8\\"|;
expect forall i :: 0 <= i < |"Da8\\"| ==> if IsLowerCase("Da8\\"[i]) then IsLowerUpperPair("Da8\\"[i], r0[i]) else r0[i] == "Da8\\"[i];
}
method {:test} Test13() {
var r0 := ToUppercase("!a_aaaaaa\U{0015}aaaWaaaaaaaaaaaaaa\r");
expect |r0| == |"!a_aaaaaa\U{0015}aaaWaaaaaaaaaaaaaa\r"|;
expect forall i :: 0 <= i < |"!a_aaaaaa\U{0015}aaaWaaaaaaaaaaaaaa\r"| ==> if IsLowerCase("!a_aaaaaa\U{0015}aaaWaaaaaaaaaaaaaa\r"[i]) then IsLowerUpperPair("!a_aaaaaa\U{0015}aaaWaaaaaaaaaaaaaa\r"[i], r0[i]) else r0[i] == "!a_aaaaaa\U{0015}aaaWaaaaaaaaaaaaaa\r"[i];
}
method {:test} Test14() {
var r0 := ToUppercase("\U{0014}[\'aaaa-aaaaXaa]a");
expect |r0| == |"\U{0014}[\'aaaa-aaaaXaa]a"|;
expect forall i :: 0 <= i < |"\U{0014}[\'aaaa-aaaaXaa]a"| ==> if IsLowerCase("\U{0014}[\'aaaa-aaaaXaa]a"[i]) then IsLowerUpperPair("\U{0014}[\'aaaa-aaaaXaa]a"[i], r0[i]) else r0[i] == "\U{0014}[\'aaaa-aaaaXaa]a"[i];
}
method {:test} Test15() {
var r0 := ToUppercase("\U{000C}(\U{0001}\U{0003}");
expect |r0| == |"\U{000C}(\U{0001}\U{0003}"|;
expect forall i :: 0 <= i < |"\U{000C}(\U{0001}\U{0003}"| ==> if IsLowerCase("\U{000C}(\U{0001}\U{0003}"[i]) then IsLowerUpperPair("\U{000C}(\U{0001}\U{0003}"[i], r0[i]) else r0[i] == "\U{000C}(\U{0001}\U{0003}"[i];
}

// REPEAT 4 - TIME: 11.7534683 s

method {:test} Test16() {
var r0 := ToUppercase("\U{0004}aaaaaaaaaaaaaaa\U{001C}aaaaaaaaaa\U{000C}a<");
expect |r0| == |"\U{0004}aaaaaaaaaaaaaaa\U{001C}aaaaaaaaaa\U{000C}a<"|;
expect forall i :: 0 <= i < |"\U{0004}aaaaaaaaaaaaaaa\U{001C}aaaaaaaaaa\U{000C}a<"| ==> if IsLowerCase("\U{0004}aaaaaaaaaaaaaaa\U{001C}aaaaaaaaaa\U{000C}a<"[i]) then IsLowerUpperPair("\U{0004}aaaaaaaaaaaaaaa\U{001C}aaaaaaaaaa\U{000C}a<"[i], r0[i]) else r0[i] == "\U{0004}aaaaaaaaaaaaaaa\U{001C}aaaaaaaaaa\U{000C}a<"[i];
}
method {:test} Test17() {
var r0 := ToUppercase("\U{0007}a\U{0018}!a");
expect |r0| == |"\U{0007}a\U{0018}!a"|;
expect forall i :: 0 <= i < |"\U{0007}a\U{0018}!a"| ==> if IsLowerCase("\U{0007}a\U{0018}!a"[i]) then IsLowerUpperPair("\U{0007}a\U{0018}!a"[i], r0[i]) else r0[i] == "\U{0007}a\U{0018}!a"[i];
}
method {:test} Test18() {
var r0 := ToUppercase("caaaaaaaaaaaaaaaaa");
expect |r0| == |"caaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"caaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("caaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("caaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "caaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test19() {
var r0 := ToUppercase("G$aaaaaaaaaaaa\0aaaaaaaa\U{0003}aa\U{0005}aa\U{0007}");
expect |r0| == |"G$aaaaaaaaaaaa\0aaaaaaaa\U{0003}aa\U{0005}aa\U{0007}"|;
expect forall i :: 0 <= i < |"G$aaaaaaaaaaaa\0aaaaaaaa\U{0003}aa\U{0005}aa\U{0007}"| ==> if IsLowerCase("G$aaaaaaaaaaaa\0aaaaaaaa\U{0003}aa\U{0005}aa\U{0007}"[i]) then IsLowerUpperPair("G$aaaaaaaaaaaa\0aaaaaaaa\U{0003}aa\U{0005}aa\U{0007}"[i], r0[i]) else r0[i] == "G$aaaaaaaaaaaa\0aaaaaaaa\U{0003}aa\U{0005}aa\U{0007}"[i];
}

// REPEAT 5 - TIME: 13.7843637 s

method {:test} Test20() {
var r0 := ToUppercase("\\aaaaaaaaaaaaaaaaaaaaaaaa(aa");
expect |r0| == |"\\aaaaaaaaaaaaaaaaaaaaaaaa(aa"|;
expect forall i :: 0 <= i < |"\\aaaaaaaaaaaaaaaaaaaaaaaa(aa"| ==> if IsLowerCase("\\aaaaaaaaaaaaaaaaaaaaaaaa(aa"[i]) then IsLowerUpperPair("\\aaaaaaaaaaaaaaaaaaaaaaaa(aa"[i], r0[i]) else r0[i] == "\\aaaaaaaaaaaaaaaaaaaaaaaa(aa"[i];
}
method {:test} Test21() {
var r0 := ToUppercase("Saaaaa");
expect |r0| == |"Saaaaa"|;
expect forall i :: 0 <= i < |"Saaaaa"| ==> if IsLowerCase("Saaaaa"[i]) then IsLowerUpperPair("Saaaaa"[i], r0[i]) else r0[i] == "Saaaaa"[i];
}
method {:test} Test22() {
var r0 := ToUppercase("Waaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Waaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Waaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Waaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Waaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Waaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test23() {
var r0 := ToUppercase("aTaaaa\0\U{0002}");
expect |r0| == |"aTaaaa\0\U{0002}"|;
expect forall i :: 0 <= i < |"aTaaaa\0\U{0002}"| ==> if IsLowerCase("aTaaaa\0\U{0002}"[i]) then IsLowerUpperPair("aTaaaa\0\U{0002}"[i], r0[i]) else r0[i] == "aTaaaa\0\U{0002}"[i];
}

// REPEAT 6 - TIME: 16.3655911 s

method {:test} Test24() {
var r0 := ToUppercase("Caaaaaaa$QGaaaaa\U{0017}aa");
expect |r0| == |"Caaaaaaa$QGaaaaa\U{0017}aa"|;
expect forall i :: 0 <= i < |"Caaaaaaa$QGaaaaa\U{0017}aa"| ==> if IsLowerCase("Caaaaaaa$QGaaaaa\U{0017}aa"[i]) then IsLowerUpperPair("Caaaaaaa$QGaaaaa\U{0017}aa"[i], r0[i]) else r0[i] == "Caaaaaaa$QGaaaaa\U{0017}aa"[i];
}
method {:test} Test25() {
var r0 := ToUppercase("Uaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Uaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Uaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Uaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Uaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Uaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test26() {
var r0 := ToUppercase("\U{C5B8}aaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{C5B8}aaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{C5B8}aaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{C5B8}aaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{C5B8}aaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{C5B8}aaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test27() {
var r0 := ToUppercase("\U{0004}aaaaa\U{0001}");
expect |r0| == |"\U{0004}aaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"\U{0004}aaaaa\U{0001}"| ==> if IsLowerCase("\U{0004}aaaaa\U{0001}"[i]) then IsLowerUpperPair("\U{0004}aaaaa\U{0001}"[i], r0[i]) else r0[i] == "\U{0004}aaaaa\U{0001}"[i];
}

// REPEAT 7 - TIME: 19.5622711 s

method {:test} Test28() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaa:");
expect |r0| == |"aaaaaaaaaaaaaaaaaaa:"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaa:"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaa:"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaa:"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaa:"[i];
}
method {:test} Test29() {
var r0 := ToUppercase("<aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"<aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"<aaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("<aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("<aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "<aaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test30() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToUppercase("(aaaaaaaaaaaaaaaaaad");
expect |r0| == |"(aaaaaaaaaaaaaaaaaad"|;
expect forall i :: 0 <= i < |"(aaaaaaaaaaaaaaaaaad"| ==> if IsLowerCase("(aaaaaaaaaaaaaaaaaad"[i]) then IsLowerUpperPair("(aaaaaaaaaaaaaaaaaad"[i], r0[i]) else r0[i] == "(aaaaaaaaaaaaaaaaaad"[i];
}

// REPEAT 8 - TIME: 21.8236683 s

method {:test} Test32() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaIaQCaK!9");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaIaQCaK!9"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaIaQCaK!9"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaIaQCaK!9"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaIaQCaK!9"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaIaQCaK!9"[i];
}
method {:test} Test33() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test34() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToUppercase("(aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"(aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"(aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("(aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("(aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "(aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 9 - TIME: 24.338658 s

method {:test} Test36() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaa(a");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaa(a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaa(a"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaa(a"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaa(a"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaa(a"[i];
}
method {:test} Test37() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test38() {
var r0 := ToUppercase("\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test39() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{0004}aaaaa"[i];
}

// REPEAT 10 - TIME: 27.5300537 s

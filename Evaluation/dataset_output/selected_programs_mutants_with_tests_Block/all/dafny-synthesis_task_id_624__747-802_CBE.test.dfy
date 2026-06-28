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
    s' := s' + [ShiftMinus32(s[i])];
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

// REPEAT 1 - TIME: 4.7092982 s

method {:test} Test4() {
var r0 := ToUppercase("&a");
expect |r0| == |"&a"|;
expect forall i :: 0 <= i < |"&a"| ==> if IsLowerCase("&a"[i]) then IsLowerUpperPair("&a"[i], r0[i]) else r0[i] == "&a"[i];
}
method {:test} Test5() {
var r0 := ToUppercase("k\U{000C}");
expect |r0| == |"k\U{000C}"|;
expect forall i :: 0 <= i < |"k\U{000C}"| ==> if IsLowerCase("k\U{000C}"[i]) then IsLowerUpperPair("k\U{000C}"[i], r0[i]) else r0[i] == "k\U{000C}"[i];
}
method {:test} Test6() {
var r0 := ToUppercase("Caaaaaaaaaaaaaa!");
expect |r0| == |"Caaaaaaaaaaaaaa!"|;
expect forall i :: 0 <= i < |"Caaaaaaaaaaaaaa!"| ==> if IsLowerCase("Caaaaaaaaaaaaaa!"[i]) then IsLowerUpperPair("Caaaaaaaaaaaaaa!"[i], r0[i]) else r0[i] == "Caaaaaaaaaaaaaa!"[i];
}
method {:test} Test7() {
var r0 := ToUppercase("x:");
expect |r0| == |"x:"|;
expect forall i :: 0 <= i < |"x:"| ==> if IsLowerCase("x:"[i]) then IsLowerUpperPair("x:"[i], r0[i]) else r0[i] == "x:"[i];
}

// REPEAT 2 - TIME: 7.5688832 s

method {:test} Test8() {
var r0 := ToUppercase("\U{0004}a8");
expect |r0| == |"\U{0004}a8"|;
expect forall i :: 0 <= i < |"\U{0004}a8"| ==> if IsLowerCase("\U{0004}a8"[i]) then IsLowerUpperPair("\U{0004}a8"[i], r0[i]) else r0[i] == "\U{0004}a8"[i];
}
method {:test} Test9() {
var r0 := ToUppercase("9a");
expect |r0| == |"9a"|;
expect forall i :: 0 <= i < |"9a"| ==> if IsLowerCase("9a"[i]) then IsLowerUpperPair("9a"[i], r0[i]) else r0[i] == "9a"[i];
}
method {:test} Test10() {
var r0 := ToUppercase("!");
expect |r0| == |"!"|;
expect forall i :: 0 <= i < |"!"| ==> if IsLowerCase("!"[i]) then IsLowerUpperPair("!"[i], r0[i]) else r0[i] == "!"[i];
}
method {:test} Test11() {
var r0 := ToUppercase(":a\U{0001}");
expect |r0| == |":a\U{0001}"|;
expect forall i :: 0 <= i < |":a\U{0001}"| ==> if IsLowerCase(":a\U{0001}"[i]) then IsLowerUpperPair(":a\U{0001}"[i], r0[i]) else r0[i] == ":a\U{0001}"[i];
}

// REPEAT 3 - TIME: 10.1326429 s

method {:test} Test12() {
var r0 := ToUppercase("\raa\U{0015}aaaWaaaaF?");
expect |r0| == |"\raa\U{0015}aaaWaaaaF?"|;
expect forall i :: 0 <= i < |"\raa\U{0015}aaaWaaaaF?"| ==> if IsLowerCase("\raa\U{0015}aaaWaaaaF?"[i]) then IsLowerUpperPair("\raa\U{0015}aaaWaaaaF?"[i], r0[i]) else r0[i] == "\raa\U{0015}aaaWaaaaF?"[i];
}
method {:test} Test13() {
var r0 := ToUppercase("af!aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"af!aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"af!aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("af!aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("af!aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "af!aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test14() {
var r0 := ToUppercase("@");
expect |r0| == |"@"|;
expect forall i :: 0 <= i < |"@"| ==> if IsLowerCase("@"[i]) then IsLowerUpperPair("@"[i], r0[i]) else r0[i] == "@"[i];
}
method {:test} Test15() {
var r0 := ToUppercase("<D\U{0002}\U{0004}");
expect |r0| == |"<D\U{0002}\U{0004}"|;
expect forall i :: 0 <= i < |"<D\U{0002}\U{0004}"| ==> if IsLowerCase("<D\U{0002}\U{0004}"[i]) then IsLowerUpperPair("<D\U{0002}\U{0004}"[i], r0[i]) else r0[i] == "<D\U{0002}\U{0004}"[i];
}

// REPEAT 4 - TIME: 12.3000473 s

method {:test} Test16() {
var r0 := ToUppercase("Qaa\U{001C}\U{0017}");
expect |r0| == |"Qaa\U{001C}\U{0017}"|;
expect forall i :: 0 <= i < |"Qaa\U{001C}\U{0017}"| ==> if IsLowerCase("Qaa\U{001C}\U{0017}"[i]) then IsLowerUpperPair("Qaa\U{001C}\U{0017}"[i], r0[i]) else r0[i] == "Qaa\U{001C}\U{0017}"[i];
}
method {:test} Test17() {
var r0 := ToUppercase("=aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"=aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"=aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("=aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("=aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "=aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test18() {
var r0 := ToUppercase("\U{0007}aaaaaaaaaaaaa\U{0018}");
expect |r0| == |"\U{0007}aaaaaaaaaaaaa\U{0018}"|;
expect forall i :: 0 <= i < |"\U{0007}aaaaaaaaaaaaa\U{0018}"| ==> if IsLowerCase("\U{0007}aaaaaaaaaaaaa\U{0018}"[i]) then IsLowerUpperPair("\U{0007}aaaaaaaaaaaaa\U{0018}"[i], r0[i]) else r0[i] == "\U{0007}aaaaaaaaaaaaa\U{0018}"[i];
}
method {:test} Test19() {
var r0 := ToUppercase("Da\U{0003}\U{0001}\U{0005}");
expect |r0| == |"Da\U{0003}\U{0001}\U{0005}"|;
expect forall i :: 0 <= i < |"Da\U{0003}\U{0001}\U{0005}"| ==> if IsLowerCase("Da\U{0003}\U{0001}\U{0005}"[i]) then IsLowerUpperPair("Da\U{0003}\U{0001}\U{0005}"[i], r0[i]) else r0[i] == "Da\U{0003}\U{0001}\U{0005}"[i];
}

// REPEAT 5 - TIME: 14.6840833 s

method {:test} Test20() {
var r0 := ToUppercase("Qaaa\U{0004}a\U{000C}");
expect |r0| == |"Qaaa\U{0004}a\U{000C}"|;
expect forall i :: 0 <= i < |"Qaaa\U{0004}a\U{000C}"| ==> if IsLowerCase("Qaaa\U{0004}a\U{000C}"[i]) then IsLowerUpperPair("Qaaa\U{0004}a\U{000C}"[i], r0[i]) else r0[i] == "Qaaa\U{0004}a\U{000C}"[i];
}
method {:test} Test21() {
var r0 := ToUppercase("!aa");
expect |r0| == |"!aa"|;
expect forall i :: 0 <= i < |"!aa"| ==> if IsLowerCase("!aa"[i]) then IsLowerUpperPair("!aa"[i], r0[i]) else r0[i] == "!aa"[i];
}
method {:test} Test22() {
var r0 := ToUppercase("e(");
expect |r0| == |"e("|;
expect forall i :: 0 <= i < |"e("| ==> if IsLowerCase("e("[i]) then IsLowerUpperPair("e("[i], r0[i]) else r0[i] == "e("[i];
}
method {:test} Test23() {
var r0 := ToUppercase("aDaaaaaaaa\U{0006}aaa\U{0008}a\U{0002}aa\U{0004}aaaaaaa\0a");
expect |r0| == |"aDaaaaaaaa\U{0006}aaa\U{0008}a\U{0002}aa\U{0004}aaaaaaa\0a"|;
expect forall i :: 0 <= i < |"aDaaaaaaaa\U{0006}aaa\U{0008}a\U{0002}aa\U{0004}aaaaaaa\0a"| ==> if IsLowerCase("aDaaaaaaaa\U{0006}aaa\U{0008}a\U{0002}aa\U{0004}aaaaaaa\0a"[i]) then IsLowerUpperPair("aDaaaaaaaa\U{0006}aaa\U{0008}a\U{0002}aa\U{0004}aaaaaaa\0a"[i], r0[i]) else r0[i] == "aDaaaaaaaa\U{0006}aaa\U{0008}a\U{0002}aa\U{0004}aaaaaaa\0a"[i];
}

// REPEAT 6 - TIME: 17.1404368 s

method {:test} Test24() {
var r0 := ToUppercase("9aaaaaT<");
expect |r0| == |"9aaaaaT<"|;
expect forall i :: 0 <= i < |"9aaaaaT<"| ==> if IsLowerCase("9aaaaaT<"[i]) then IsLowerUpperPair("9aaaaaT<"[i], r0[i]) else r0[i] == "9aaaaaT<"[i];
}
method {:test} Test25() {
var r0 := ToUppercase("X");
expect |r0| == |"X"|;
expect forall i :: 0 <= i < |"X"| ==> if IsLowerCase("X"[i]) then IsLowerUpperPair("X"[i], r0[i]) else r0[i] == "X"[i];
}
method {:test} Test26() {
var r0 := ToUppercase("\taaaaa>aaaa");
expect |r0| == |"\taaaaa>aaaa"|;
expect forall i :: 0 <= i < |"\taaaaa>aaaa"| ==> if IsLowerCase("\taaaaa>aaaa"[i]) then IsLowerUpperPair("\taaaaa>aaaa"[i], r0[i]) else r0[i] == "\taaaaa>aaaa"[i];
}
method {:test} Test27() {
var r0 := ToUppercase("a$aaaaaa\U{0003}aaaaaaaa\U{0001}aaaaaaaaaa");
expect |r0| == |"a$aaaaaa\U{0003}aaaaaaaa\U{0001}aaaaaaaaaa"|;
expect forall i :: 0 <= i < |"a$aaaaaa\U{0003}aaaaaaaa\U{0001}aaaaaaaaaa"| ==> if IsLowerCase("a$aaaaaa\U{0003}aaaaaaaa\U{0001}aaaaaaaaaa"[i]) then IsLowerUpperPair("a$aaaaaa\U{0003}aaaaaaaa\U{0001}aaaaaaaaaa"[i], r0[i]) else r0[i] == "a$aaaaaa\U{0003}aaaaaaaa\U{0001}aaaaaaaaaa"[i];
}

// REPEAT 7 - TIME: 19.8996951 s

method {:test} Test28() {
var r0 := ToUppercase("(aaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\\");
expect |r0| == |"(aaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\\"|;
expect forall i :: 0 <= i < |"(aaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\\"| ==> if IsLowerCase("(aaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\\"[i]) then IsLowerUpperPair("(aaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\\"[i], r0[i]) else r0[i] == "(aaaaaaaaaaaaaaaaaaaaaaaa\U{000C}\\"[i];
}
method {:test} Test29() {
var r0 := ToUppercase("Caaaaaaaaaaaaaaaaaaaaaaaa?a");
expect |r0| == |"Caaaaaaaaaaaaaaaaaaaaaaaa?a"|;
expect forall i :: 0 <= i < |"Caaaaaaaaaaaaaaaaaaaaaaaa?a"| ==> if IsLowerCase("Caaaaaaaaaaaaaaaaaaaaaaaa?a"[i]) then IsLowerUpperPair("Caaaaaaaaaaaaaaaaaaaaaaaa?a"[i], r0[i]) else r0[i] == "Caaaaaaaaaaaaaaaaaaaaaaaa?a"[i];
}
method {:test} Test30() {
var r0 := ToUppercase("{aaa");
expect |r0| == |"{aaa"|;
expect forall i :: 0 <= i < |"{aaa"| ==> if IsLowerCase("{aaa"[i]) then IsLowerUpperPair("{aaa"[i], r0[i]) else r0[i] == "{aaa"[i];
}
method {:test} Test31() {
var r0 := ToUppercase("aTaaaaaaaa\U{0003}a\U{0001}a\U{0007}\taaaaaaaa\U{0005}aaaa\U{000B}");
expect |r0| == |"aTaaaaaaaa\U{0003}a\U{0001}a\U{0007}\taaaaaaaa\U{0005}aaaa\U{000B}"|;
expect forall i :: 0 <= i < |"aTaaaaaaaa\U{0003}a\U{0001}a\U{0007}\taaaaaaaa\U{0005}aaaa\U{000B}"| ==> if IsLowerCase("aTaaaaaaaa\U{0003}a\U{0001}a\U{0007}\taaaaaaaa\U{0005}aaaa\U{000B}"[i]) then IsLowerUpperPair("aTaaaaaaaa\U{0003}a\U{0001}a\U{0007}\taaaaaaaa\U{0005}aaaa\U{000B}"[i], r0[i]) else r0[i] == "aTaaaaaaaa\U{0003}a\U{0001}a\U{0007}\taaaaaaaa\U{0005}aaaa\U{000B}"[i];
}

// REPEAT 8 - TIME: 22.5626035 s

method {:test} Test32() {
var r0 := ToUppercase("&aaaaaaaa");
expect |r0| == |"&aaaaaaaa"|;
expect forall i :: 0 <= i < |"&aaaaaaaa"| ==> if IsLowerCase("&aaaaaaaa"[i]) then IsLowerUpperPair("&aaaaaaaa"[i], r0[i]) else r0[i] == "&aaaaaaaa"[i];
}
method {:test} Test33() {
var r0 := ToUppercase("\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{000C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test34() {
var r0 := ToUppercase("\U{0015}aa_Wa");
expect |r0| == |"\U{0015}aa_Wa"|;
expect forall i :: 0 <= i < |"\U{0015}aa_Wa"| ==> if IsLowerCase("\U{0015}aa_Wa"[i]) then IsLowerUpperPair("\U{0015}aa_Wa"[i], r0[i]) else r0[i] == "\U{0015}aa_Wa"[i];
}
method {:test} Test35() {
var r0 := ToUppercase("a(aaaaaaa\0");
expect |r0| == |"a(aaaaaaa\0"|;
expect forall i :: 0 <= i < |"a(aaaaaaa\0"| ==> if IsLowerCase("a(aaaaaaa\0"[i]) then IsLowerUpperPair("a(aaaaaaa\0"[i], r0[i]) else r0[i] == "a(aaaaaaa\0"[i];
}

// REPEAT 9 - TIME: 26.1053629 s

method {:test} Test36() {
var r0 := ToUppercase("\U{001C}aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa");
expect |r0| == |"\U{001C}aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{001C}aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{001C}aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{001C}aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{001C}aaaaaaaaaaa\U{0004}aaaaaaaaaaaaaaa"[i];
}
method {:test} Test37() {
var r0 := ToUppercase("Vaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Vaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Vaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Vaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Vaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Vaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test38() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test39() {
var r0 := ToUppercase("Taaaaaaaaaa\U{0003}aaaaaaaaaaaaaa\U{0001}");
expect |r0| == |"Taaaaaaaaaa\U{0003}aaaaaaaaaaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |"Taaaaaaaaaa\U{0003}aaaaaaaaaaaaaa\U{0001}"| ==> if IsLowerCase("Taaaaaaaaaa\U{0003}aaaaaaaaaaaaaa\U{0001}"[i]) then IsLowerUpperPair("Taaaaaaaaaa\U{0003}aaaaaaaaaaaaaa\U{0001}"[i], r0[i]) else r0[i] == "Taaaaaaaaaa\U{0003}aaaaaaaaaaaaaa\U{0001}"[i];
}

// REPEAT 10 - TIME: 28.9980259 s

// dafny-synthesis_task_id_477.dfy

predicate IsUpperCase(c: char)
{
  65 <= c as int <= 90
}

predicate IsUpperLowerPair(C: char, c: char)
{
  C as int == c as int - 32
}

function Shift32(c: char): char
{
  ((c as int + 32) % 128) as char
}

method {:testEntry} ToLowercase(s: string) returns (v: string)
  ensures |v| == |s|
  ensures forall i :: 0 <= i < |s| ==> if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
  var s': string := ['a', 'b', 'c'];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i && IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsUpperCase(s[k]) ==> s[k] == s'[k]
  {
    if IsUpperCase(s[i]) {
      s' := s' + [Shift32(s[i])];
    } else {
      s' := s' + [s[i]];
    }
  }
  return s';
}


method {:test} Test0() {
var r0 := ToLowercase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test2() {
var r0 := ToLowercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test3() {
var r0 := ToLowercase("a@");
expect |r0| == |"a@"|;
expect forall i :: 0 <= i < |"a@"| ==> if IsUpperCase("a@"[i]) then IsUpperLowerPair("a@"[i], r0[i]) else r0[i] == "a@"[i];
}

// REPEAT 1 - TIME: 4.7403902 s

method {:test} Test4() {
var r0 := ToLowercase("C");
expect |r0| == |"C"|;
expect forall i :: 0 <= i < |"C"| ==> if IsUpperCase("C"[i]) then IsUpperLowerPair("C"[i], r0[i]) else r0[i] == "C"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("Ya");
expect |r0| == |"Ya"|;
expect forall i :: 0 <= i < |"Ya"| ==> if IsUpperCase("Ya"[i]) then IsUpperLowerPair("Ya"[i], r0[i]) else r0[i] == "Ya"[i];
}
method {:test} Test6() {
var r0 := ToLowercase("[aaaaaaaaaaaaaaaaa.");
expect |r0| == |"[aaaaaaaaaaaaaaaaa."|;
expect forall i :: 0 <= i < |"[aaaaaaaaaaaaaaaaa."| ==> if IsUpperCase("[aaaaaaaaaaaaaaaaa."[i]) then IsUpperLowerPair("[aaaaaaaaaaaaaaaaa."[i], r0[i]) else r0[i] == "[aaaaaaaaaaaaaaaaa."[i];
}
method {:test} Test7() {
var r0 := ToLowercase("[");
expect |r0| == |"["|;
expect forall i :: 0 <= i < |"["| ==> if IsUpperCase("["[i]) then IsUpperLowerPair("["[i], r0[i]) else r0[i] == "["[i];
}

// REPEAT 2 - TIME: 7.7445525 s

method {:test} Test8() {
var r0 := ToLowercase("\U{000F}a0");
expect |r0| == |"\U{000F}a0"|;
expect forall i :: 0 <= i < |"\U{000F}a0"| ==> if IsUpperCase("\U{000F}a0"[i]) then IsUpperLowerPair("\U{000F}a0"[i], r0[i]) else r0[i] == "\U{000F}a0"[i];
}
method {:test} Test9() {
var r0 := ToLowercase(" a");
expect |r0| == |" a"|;
expect forall i :: 0 <= i < |" a"| ==> if IsUpperCase(" a"[i]) then IsUpperLowerPair(" a"[i], r0[i]) else r0[i] == " a"[i];
}
method {:test} Test10() {
var r0 := ToLowercase("<&aaaaaaaaaaaaaaa)aaaaaaa\U{0005}");
expect |r0| == |"<&aaaaaaaaaaaaaaa)aaaaaaa\U{0005}"|;
expect forall i :: 0 <= i < |"<&aaaaaaaaaaaaaaa)aaaaaaa\U{0005}"| ==> if IsUpperCase("<&aaaaaaaaaaaaaaa)aaaaaaa\U{0005}"[i]) then IsUpperLowerPair("<&aaaaaaaaaaaaaaa)aaaaaaa\U{0005}"[i], r0[i]) else r0[i] == "<&aaaaaaaaaaaaaaa)aaaaaaa\U{0005}"[i];
}
method {:test} Test11() {
var r0 := ToLowercase("a\U{001A}\0");
expect |r0| == |"a\U{001A}\0"|;
expect forall i :: 0 <= i < |"a\U{001A}\0"| ==> if IsUpperCase("a\U{001A}\0"[i]) then IsUpperLowerPair("a\U{001A}\0"[i], r0[i]) else r0[i] == "a\U{001A}\0"[i];
}

// REPEAT 3 - TIME: 10.6444999 s

method {:test} Test12() {
var r0 := ToLowercase("-aaaaaaaaaaaaaaaaaaa aaaaaaa-");
expect |r0| == |"-aaaaaaaaaaaaaaaaaaa aaaaaaa-"|;
expect forall i :: 0 <= i < |"-aaaaaaaaaaaaaaaaaaa aaaaaaa-"| ==> if IsUpperCase("-aaaaaaaaaaaaaaaaaaa aaaaaaa-"[i]) then IsUpperLowerPair("-aaaaaaaaaaaaaaaaaaa aaaaaaa-"[i], r0[i]) else r0[i] == "-aaaaaaaaaaaaaaaaaaa aaaaaaa-"[i];
}
method {:test} Test13() {
var r0 := ToLowercase(">a2aaaaaaaaaaaaaaaaa");
expect |r0| == |">a2aaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |">a2aaaaaaaaaaaaaaaaa"| ==> if IsUpperCase(">a2aaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair(">a2aaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == ">a2aaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test14() {
var r0 := ToLowercase("\U{0007}");
expect |r0| == |"\U{0007}"|;
expect forall i :: 0 <= i < |"\U{0007}"| ==> if IsUpperCase("\U{0007}"[i]) then IsUpperLowerPair("\U{0007}"[i], r0[i]) else r0[i] == "\U{0007}"[i];
}
method {:test} Test15() {
var r0 := ToLowercase("a\U{000F}a\U{0001}");
expect |r0| == |"a\U{000F}a\U{0001}"|;
expect forall i :: 0 <= i < |"a\U{000F}a\U{0001}"| ==> if IsUpperCase("a\U{000F}a\U{0001}"[i]) then IsUpperLowerPair("a\U{000F}a\U{0001}"[i], r0[i]) else r0[i] == "a\U{000F}a\U{0001}"[i];
}

// REPEAT 4 - TIME: 13.2168367 s

method {:test} Test16() {
var r0 := ToLowercase("1aa->aa-aaaaaaaaa a\U{0003}2");
expect |r0| == |"1aa->aa-aaaaaaaaa a\U{0003}2"|;
expect forall i :: 0 <= i < |"1aa->aa-aaaaaaaaa a\U{0003}2"| ==> if IsUpperCase("1aa->aa-aaaaaaaaa a\U{0003}2"[i]) then IsUpperLowerPair("1aa->aa-aaaaaaaaa a\U{0003}2"[i], r0[i]) else r0[i] == "1aa->aa-aaaaaaaaa a\U{0003}2"[i];
}
method {:test} Test17() {
var r0 := ToLowercase(">aa)aaaa\naaa7.aaaaa");
expect |r0| == |">aa)aaaa\naaa7.aaaaa"|;
expect forall i :: 0 <= i < |">aa)aaaa\naaa7.aaaaa"| ==> if IsUpperCase(">aa)aaaa\naaa7.aaaaa"[i]) then IsUpperLowerPair(">aa)aaaa\naaa7.aaaaa"[i], r0[i]) else r0[i] == ">aa)aaaa\naaa7.aaaaa"[i];
}
method {:test} Test18() {
var r0 := ToLowercase(",a\U{0007}");
expect |r0| == |",a\U{0007}"|;
expect forall i :: 0 <= i < |",a\U{0007}"| ==> if IsUpperCase(",a\U{0007}"[i]) then IsUpperLowerPair(",a\U{0007}"[i], r0[i]) else r0[i] == ",a\U{0007}"[i];
}
method {:test} Test19() {
var r0 := ToLowercase("a\U{000F}a\U{0002}\U{0004}a\0a");
expect |r0| == |"a\U{000F}a\U{0002}\U{0004}a\0a"|;
expect forall i :: 0 <= i < |"a\U{000F}a\U{0002}\U{0004}a\0a"| ==> if IsUpperCase("a\U{000F}a\U{0002}\U{0004}a\0a"[i]) then IsUpperLowerPair("a\U{000F}a\U{0002}\U{0004}a\0a"[i], r0[i]) else r0[i] == "a\U{000F}a\U{0002}\U{0004}a\0a"[i];
}

// REPEAT 5 - TIME: 15.5273977 s

method {:test} Test20() {
var r0 := ToLowercase("\U{0018}aa>=");
expect |r0| == |"\U{0018}aa>="|;
expect forall i :: 0 <= i < |"\U{0018}aa>="| ==> if IsUpperCase("\U{0018}aa>="[i]) then IsUpperLowerPair("\U{0018}aa>="[i], r0[i]) else r0[i] == "\U{0018}aa>="[i];
}
method {:test} Test21() {
var r0 := ToLowercase("S7a(aa");
expect |r0| == |"S7a(aa"|;
expect forall i :: 0 <= i < |"S7a(aa"| ==> if IsUpperCase("S7a(aa"[i]) then IsUpperLowerPair("S7a(aa"[i], r0[i]) else r0[i] == "S7a(aa"[i];
}
method {:test} Test22() {
var r0 := ToLowercase("/aaaaaaaaaaaaaaaaaaaaaaaaaaaa>");
expect |r0| == |"/aaaaaaaaaaaaaaaaaaaaaaaaaaaa>"|;
expect forall i :: 0 <= i < |"/aaaaaaaaaaaaaaaaaaaaaaaaaaaa>"| ==> if IsUpperCase("/aaaaaaaaaaaaaaaaaaaaaaaaaaaa>"[i]) then IsUpperLowerPair("/aaaaaaaaaaaaaaaaaaaaaaaaaaaa>"[i], r0[i]) else r0[i] == "/aaaaaaaaaaaaaaaaaaaaaaaaaaaa>"[i];
}
method {:test} Test23() {
var r0 := ToLowercase("aaaaaa aaaaaaaaaaaa a-aaaaaaa-");
expect |r0| == |"aaaaaa aaaaaaaaaaaa a-aaaaaaa-"|;
expect forall i :: 0 <= i < |"aaaaaa aaaaaaaaaaaa a-aaaaaaa-"| ==> if IsUpperCase("aaaaaa aaaaaaaaaaaa a-aaaaaaa-"[i]) then IsUpperLowerPair("aaaaaa aaaaaaaaaaaa a-aaaaaaa-"[i], r0[i]) else r0[i] == "aaaaaa aaaaaaaaaaaa a-aaaaaaa-"[i];
}

// REPEAT 6 - TIME: 18.1242202 s

method {:test} Test24() {
var r0 := ToLowercase("2aaaa \U{000F}");
expect |r0| == |"2aaaa \U{000F}"|;
expect forall i :: 0 <= i < |"2aaaa \U{000F}"| ==> if IsUpperCase("2aaaa \U{000F}"[i]) then IsUpperLowerPair("2aaaa \U{000F}"[i], r0[i]) else r0[i] == "2aaaa \U{000F}"[i];
}
method {:test} Test25() {
var r0 := ToLowercase("=aa>");
expect |r0| == |"=aa>"|;
expect forall i :: 0 <= i < |"=aa>"| ==> if IsUpperCase("=aa>"[i]) then IsUpperLowerPair("=aa>"[i], r0[i]) else r0[i] == "=aa>"[i];
}
method {:test} Test26() {
var r0 := ToLowercase("\U{0010}a\U{0007}a");
expect |r0| == |"\U{0010}a\U{0007}a"|;
expect forall i :: 0 <= i < |"\U{0010}a\U{0007}a"| ==> if IsUpperCase("\U{0010}a\U{0007}a"[i]) then IsUpperLowerPair("\U{0010}a\U{0007}a"[i], r0[i]) else r0[i] == "\U{0010}a\U{0007}a"[i];
}
method {:test} Test27() {
var r0 := ToLowercase("a\U{001A}aaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}aaaaaaa");
expect |r0| == |"a\U{001A}aaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}aaaaaaa"|;
expect forall i :: 0 <= i < |"a\U{001A}aaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}aaaaaaa"| ==> if IsUpperCase("a\U{001A}aaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}aaaaaaa"[i]) then IsUpperLowerPair("a\U{001A}aaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}aaaaaaa"[i], r0[i]) else r0[i] == "a\U{001A}aaaaaa\0aaaaaaaaaa\U{0002}a\U{0004}aaaaaaa"[i];
}

// REPEAT 7 - TIME: 21.1302566 s

method {:test} Test28() {
var r0 := ToLowercase("aaaaaaaaaaaaaa aaaaaaaa1aaa-");
expect |r0| == |"aaaaaaaaaaaaaa aaaaaaaa1aaa-"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaa aaaaaaaa1aaa-"| ==> if IsUpperCase("aaaaaaaaaaaaaa aaaaaaaa1aaa-"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaa aaaaaaaa1aaa-"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaa aaaaaaaa1aaa-"[i];
}
method {:test} Test29() {
var r0 := ToLowercase("%aaaaaa");
expect |r0| == |"%aaaaaa"|;
expect forall i :: 0 <= i < |"%aaaaaa"| ==> if IsUpperCase("%aaaaaa"[i]) then IsUpperLowerPair("%aaaaaa"[i], r0[i]) else r0[i] == "%aaaaaa"[i];
}
method {:test} Test30() {
var r0 := ToLowercase("\U{0017}aaaaaaaaa");
expect |r0| == |"\U{0017}aaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0017}aaaaaaaaa"| ==> if IsUpperCase("\U{0017}aaaaaaaaa"[i]) then IsUpperLowerPair("\U{0017}aaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0017}aaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToLowercase("a\U{001A}aaaaaaaaaaaaaaaaa\0a\U{0002}aaaaaaaa");
expect |r0| == |"a\U{001A}aaaaaaaaaaaaaaaaa\0a\U{0002}aaaaaaaa"|;
expect forall i :: 0 <= i < |"a\U{001A}aaaaaaaaaaaaaaaaa\0a\U{0002}aaaaaaaa"| ==> if IsUpperCase("a\U{001A}aaaaaaaaaaaaaaaaa\0a\U{0002}aaaaaaaa"[i]) then IsUpperLowerPair("a\U{001A}aaaaaaaaaaaaaaaaa\0a\U{0002}aaaaaaaa"[i], r0[i]) else r0[i] == "a\U{001A}aaaaaaaaaaaaaaaaa\0a\U{0002}aaaaaaaa"[i];
}

// REPEAT 8 - TIME: 23.8611242 s

method {:test} Test32() {
var r0 := ToLowercase(" aaaaaaa\U{0010}");
expect |r0| == |" aaaaaaa\U{0010}"|;
expect forall i :: 0 <= i < |" aaaaaaa\U{0010}"| ==> if IsUpperCase(" aaaaaaa\U{0010}"[i]) then IsUpperLowerPair(" aaaaaaa\U{0010}"[i], r0[i]) else r0[i] == " aaaaaaa\U{0010}"[i];
}
method {:test} Test33() {
var r0 := ToLowercase("\U{0003}aaaa");
expect |r0| == |"\U{0003}aaaa"|;
expect forall i :: 0 <= i < |"\U{0003}aaaa"| ==> if IsUpperCase("\U{0003}aaaa"[i]) then IsUpperLowerPair("\U{0003}aaaa"[i], r0[i]) else r0[i] == "\U{0003}aaaa"[i];
}
method {:test} Test34() {
var r0 := ToLowercase("\U{0015}aaaaaaaa");
expect |r0| == |"\U{0015}aaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0015}aaaaaaaa"| ==> if IsUpperCase("\U{0015}aaaaaaaa"[i]) then IsUpperLowerPair("\U{0015}aaaaaaaa"[i], r0[i]) else r0[i] == "\U{0015}aaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToLowercase("aaaaaa \U{0003}\U{0001}");
expect |r0| == |"aaaaaa \U{0003}\U{0001}"|;
expect forall i :: 0 <= i < |"aaaaaa \U{0003}\U{0001}"| ==> if IsUpperCase("aaaaaa \U{0003}\U{0001}"[i]) then IsUpperLowerPair("aaaaaa \U{0003}\U{0001}"[i], r0[i]) else r0[i] == "aaaaaa \U{0003}\U{0001}"[i];
}

// REPEAT 9 - TIME: 26.7310327 s

method {:test} Test36() {
var r0 := ToLowercase("-aaaaaaaaaaaaaaaaaaaaaaaa a");
expect |r0| == |"-aaaaaaaaaaaaaaaaaaaaaaaa a"|;
expect forall i :: 0 <= i < |"-aaaaaaaaaaaaaaaaaaaaaaaa a"| ==> if IsUpperCase("-aaaaaaaaaaaaaaaaaaaaaaaa a"[i]) then IsUpperLowerPair("-aaaaaaaaaaaaaaaaaaaaaaaa a"[i], r0[i]) else r0[i] == "-aaaaaaaaaaaaaaaaaaaaaaaa a"[i];
}
method {:test} Test37() {
var r0 := ToLowercase("W\U{0014}");
expect |r0| == |"W\U{0014}"|;
expect forall i :: 0 <= i < |"W\U{0014}"| ==> if IsUpperCase("W\U{0014}"[i]) then IsUpperLowerPair("W\U{0014}"[i], r0[i]) else r0[i] == "W\U{0014}"[i];
}
method {:test} Test38() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test39() {
var r0 := ToLowercase("aaaaaaa\U{0010}a\U{0001}aaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaa\U{0010}a\U{0001}aaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaa\U{0010}a\U{0001}aaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaa\U{0010}a\U{0001}aaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaa\U{0010}a\U{0001}aaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaa\U{0010}a\U{0001}aaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 10 - TIME: 29.808219 s

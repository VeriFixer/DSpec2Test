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


predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method {:testEntry} ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsUpperCase(s[k]) ==> s[k] == s'[k]
    {
        if IsUpperCase(s[i])
        {
            s' := s' + [Shift32(s[i])];
        }
        else 
        {
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

// REPEAT 1 - TIME: 4.8449913 s

method {:test} Test4() {
var r0 := ToLowercase("M");
expect |r0| == |"M"|;
expect forall i :: 0 <= i < |"M"| ==> if IsUpperCase("M"[i]) then IsUpperLowerPair("M"[i], r0[i]) else r0[i] == "M"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("[");
expect |r0| == |"["|;
expect forall i :: 0 <= i < |"["| ==> if IsUpperCase("["[i]) then IsUpperLowerPair("["[i], r0[i]) else r0[i] == "["[i];
}
method {:test} Test6() {
var r0 := ToLowercase("\U{0015}aaaaaaaaaaaaaa%");
expect |r0| == |"\U{0015}aaaaaaaaaaaaaa%"|;
expect forall i :: 0 <= i < |"\U{0015}aaaaaaaaaaaaaa%"| ==> if IsUpperCase("\U{0015}aaaaaaaaaaaaaa%"[i]) then IsUpperLowerPair("\U{0015}aaaaaaaaaaaaaa%"[i], r0[i]) else r0[i] == "\U{0015}aaaaaaaaaaaaaa%"[i];
}
method {:test} Test7() {
var r0 := ToLowercase("\U{001A}CD");
expect |r0| == |"\U{001A}CD"|;
expect forall i :: 0 <= i < |"\U{001A}CD"| ==> if IsUpperCase("\U{001A}CD"[i]) then IsUpperLowerPair("\U{001A}CD"[i], r0[i]) else r0[i] == "\U{001A}CD"[i];
}

// REPEAT 2 - TIME: 7.8627402 s

method {:test} Test8() {
var r0 := ToLowercase("\U{0010}aa");
expect |r0| == |"\U{0010}aa"|;
expect forall i :: 0 <= i < |"\U{0010}aa"| ==> if IsUpperCase("\U{0010}aa"[i]) then IsUpperLowerPair("\U{0010}aa"[i], r0[i]) else r0[i] == "\U{0010}aa"[i];
}
method {:test} Test9() {
var r0 := ToLowercase(">a2");
expect |r0| == |">a2"|;
expect forall i :: 0 <= i < |">a2"| ==> if IsUpperCase(">a2"[i]) then IsUpperLowerPair(">a2"[i], r0[i]) else r0[i] == ">a2"[i];
}
method {:test} Test10() {
var r0 := ToLowercase(".aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |".aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |".aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase(".aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair(".aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == ".aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test11() {
var r0 := ToLowercase("\U{001A}");
expect |r0| == |"\U{001A}"|;
expect forall i :: 0 <= i < |"\U{001A}"| ==> if IsUpperCase("\U{001A}"[i]) then IsUpperLowerPair("\U{001A}"[i], r0[i]) else r0[i] == "\U{001A}"[i];
}

// REPEAT 3 - TIME: 9.8943418 s

method {:test} Test12() {
var r0 := ToLowercase("\U{000F}a0a");
expect |r0| == |"\U{000F}a0a"|;
expect forall i :: 0 <= i < |"\U{000F}a0a"| ==> if IsUpperCase("\U{000F}a0a"[i]) then IsUpperLowerPair("\U{000F}a0a"[i], r0[i]) else r0[i] == "\U{000F}a0a"[i];
}
method {:test} Test13() {
var r0 := ToLowercase("?%a");
expect |r0| == |"?%a"|;
expect forall i :: 0 <= i < |"?%a"| ==> if IsUpperCase("?%a"[i]) then IsUpperLowerPair("?%a"[i], r0[i]) else r0[i] == "?%a"[i];
}
method {:test} Test14() {
var r0 := ToLowercase("\U{0017}\n");
expect |r0| == |"\U{0017}\n"|;
expect forall i :: 0 <= i < |"\U{0017}\n"| ==> if IsUpperCase("\U{0017}\n"[i]) then IsUpperLowerPair("\U{0017}\n"[i], r0[i]) else r0[i] == "\U{0017}\n"[i];
}
method {:test} Test15() {
var r0 := ToLowercase("\U{001B}");
expect |r0| == |"\U{001B}"|;
expect forall i :: 0 <= i < |"\U{001B}"| ==> if IsUpperCase("\U{001B}"[i]) then IsUpperLowerPair("\U{001B}"[i], r0[i]) else r0[i] == "\U{001B}"[i];
}

// REPEAT 4 - TIME: 12.2499168 s

method {:test} Test16() {
var r0 := ToLowercase("\U{0010}a a\U{000F}aaaaaaaaaaaaaa ");
expect |r0| == |"\U{0010}a a\U{000F}aaaaaaaaaaaaaa "|;
expect forall i :: 0 <= i < |"\U{0010}a a\U{000F}aaaaaaaaaaaaaa "| ==> if IsUpperCase("\U{0010}a a\U{000F}aaaaaaaaaaaaaa "[i]) then IsUpperLowerPair("\U{0010}a a\U{000F}aaaaaaaaaaaaaa "[i], r0[i]) else r0[i] == "\U{0010}a a\U{000F}aaaaaaaaaaaaaa "[i];
}
method {:test} Test17() {
var r0 := ToLowercase("?aaaa");
expect |r0| == |"?aaaa"|;
expect forall i :: 0 <= i < |"?aaaa"| ==> if IsUpperCase("?aaaa"[i]) then IsUpperLowerPair("?aaaa"[i], r0[i]) else r0[i] == "?aaaa"[i];
}
method {:test} Test18() {
var r0 := ToLowercase("\U{CFBF}\U{CFBE}aaaaaaaaaaaaa\U{0013}aaaaaaaa\U{001B}aaa\U{C7D8}");
expect |r0| == |"\U{CFBF}\U{CFBE}aaaaaaaaaaaaa\U{0013}aaaaaaaa\U{001B}aaa\U{C7D8}"|;
expect forall i :: 0 <= i < |"\U{CFBF}\U{CFBE}aaaaaaaaaaaaa\U{0013}aaaaaaaa\U{001B}aaa\U{C7D8}"| ==> if IsUpperCase("\U{CFBF}\U{CFBE}aaaaaaaaaaaaa\U{0013}aaaaaaaa\U{001B}aaa\U{C7D8}"[i]) then IsUpperLowerPair("\U{CFBF}\U{CFBE}aaaaaaaaaaaaa\U{0013}aaaaaaaa\U{001B}aaa\U{C7D8}"[i], r0[i]) else r0[i] == "\U{CFBF}\U{CFBE}aaaaaaaaaaaaa\U{0013}aaaaaaaa\U{001B}aaa\U{C7D8}"[i];
}
method {:test} Test19() {
var r0 := ToLowercase("\U{000F}\U{0010}\U{0003}a\U{0005}a\0aaaaaaaaaaaa\U{0007}");
expect |r0| == |"\U{000F}\U{0010}\U{0003}a\U{0005}a\0aaaaaaaaaaaa\U{0007}"|;
expect forall i :: 0 <= i < |"\U{000F}\U{0010}\U{0003}a\U{0005}a\0aaaaaaaaaaaa\U{0007}"| ==> if IsUpperCase("\U{000F}\U{0010}\U{0003}a\U{0005}a\0aaaaaaaaaaaa\U{0007}"[i]) then IsUpperLowerPair("\U{000F}\U{0010}\U{0003}a\U{0005}a\0aaaaaaaaaaaa\U{0007}"[i], r0[i]) else r0[i] == "\U{000F}\U{0010}\U{0003}a\U{0005}a\0aaaaaaaaaaaa\U{0007}"[i];
}

// REPEAT 5 - TIME: 14.5029252 s

method {:test} Test20() {
var r0 := ToLowercase(" aaaa aaaaaaaaaa2a\U{000F}-a");
expect |r0| == |" aaaa aaaaaaaaaa2a\U{000F}-a"|;
expect forall i :: 0 <= i < |" aaaa aaaaaaaaaa2a\U{000F}-a"| ==> if IsUpperCase(" aaaa aaaaaaaaaa2a\U{000F}-a"[i]) then IsUpperLowerPair(" aaaa aaaaaaaaaa2a\U{000F}-a"[i], r0[i]) else r0[i] == " aaaa aaaaaaaaaa2a\U{000F}-a"[i];
}
method {:test} Test21() {
var r0 := ToLowercase("\U{0014}aaaaaaaaaaaa\U{0003}aaaaaaaaaaaa");
expect |r0| == |"\U{0014}aaaaaaaaaaaa\U{0003}aaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0014}aaaaaaaaaaaa\U{0003}aaaaaaaaaaaa"| ==> if IsUpperCase("\U{0014}aaaaaaaaaaaa\U{0003}aaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0014}aaaaaaaaaaaa\U{0003}aaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0014}aaaaaaaaaaaa\U{0003}aaaaaaaaaaaa"[i];
}
method {:test} Test22() {
var r0 := ToLowercase("\U{0007}\U{0007}\U{0013}aa\U{001B}aaaaaaaaa$a");
expect |r0| == |"\U{0007}\U{0007}\U{0013}aa\U{001B}aaaaaaaaa$a"|;
expect forall i :: 0 <= i < |"\U{0007}\U{0007}\U{0013}aa\U{001B}aaaaaaaaa$a"| ==> if IsUpperCase("\U{0007}\U{0007}\U{0013}aa\U{001B}aaaaaaaaa$a"[i]) then IsUpperLowerPair("\U{0007}\U{0007}\U{0013}aa\U{001B}aaaaaaaaa$a"[i], r0[i]) else r0[i] == "\U{0007}\U{0007}\U{0013}aa\U{001B}aaaaaaaaa$a"[i];
}
method {:test} Test23() {
var r0 := ToLowercase("a1aa\U{0003}aaaaaaaaaaaaa\U{0014}a%aaaa>a2-\U{0015}");
expect |r0| == |"a1aa\U{0003}aaaaaaaaaaaaa\U{0014}a%aaaa>a2-\U{0015}"|;
expect forall i :: 0 <= i < |"a1aa\U{0003}aaaaaaaaaaaaa\U{0014}a%aaaa>a2-\U{0015}"| ==> if IsUpperCase("a1aa\U{0003}aaaaaaaaaaaaa\U{0014}a%aaaa>a2-\U{0015}"[i]) then IsUpperLowerPair("a1aa\U{0003}aaaaaaaaaaaaa\U{0014}a%aaaa>a2-\U{0015}"[i], r0[i]) else r0[i] == "a1aa\U{0003}aaaaaaaaaaaaa\U{0014}a%aaaa>a2-\U{0015}"[i];
}

// REPEAT 6 - TIME: 16.7348153 s

method {:test} Test24() {
var r0 := ToLowercase(">aaa1aaaaa aaaaaa-aaa-");
expect |r0| == |">aaa1aaaaa aaaaaa-aaa-"|;
expect forall i :: 0 <= i < |">aaa1aaaaa aaaaaa-aaa-"| ==> if IsUpperCase(">aaa1aaaaa aaaaaa-aaa-"[i]) then IsUpperLowerPair(">aaa1aaaaa aaaaaa-aaa-"[i], r0[i]) else r0[i] == ">aaa1aaaaa aaaaaa-aaa-"[i];
}
method {:test} Test25() {
var r0 := ToLowercase("\U{0003}a>aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0003}a>aaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0003}a>aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("\U{0003}a>aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0003}a>aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0003}a>aaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test26() {
var r0 := ToLowercase("\U{0017}a>aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0017}a>aaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0017}a>aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("\U{0017}a>aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0017}a>aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0017}a>aaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test27() {
var r0 := ToLowercase("a<aaaaaaaaaaaaaaa\U{0003}\U{0001}aaaaaaaa\U{0007}\U{0005}\t");
expect |r0| == |"a<aaaaaaaaaaaaaaa\U{0003}\U{0001}aaaaaaaa\U{0007}\U{0005}\t"|;
expect forall i :: 0 <= i < |"a<aaaaaaaaaaaaaaa\U{0003}\U{0001}aaaaaaaa\U{0007}\U{0005}\t"| ==> if IsUpperCase("a<aaaaaaaaaaaaaaa\U{0003}\U{0001}aaaaaaaa\U{0007}\U{0005}\t"[i]) then IsUpperLowerPair("a<aaaaaaaaaaaaaaa\U{0003}\U{0001}aaaaaaaa\U{0007}\U{0005}\t"[i], r0[i]) else r0[i] == "a<aaaaaaaaaaaaaaa\U{0003}\U{0001}aaaaaaaa\U{0007}\U{0005}\t"[i];
}

// REPEAT 7 - TIME: 19.2933341 s

method {:test} Test28() {
var r0 := ToLowercase(">aaaaaaaaaaaaaaaa1aaaaaaaaa--a");
expect |r0| == |">aaaaaaaaaaaaaaaa1aaaaaaaaa--a"|;
expect forall i :: 0 <= i < |">aaaaaaaaaaaaaaaa1aaaaaaaaa--a"| ==> if IsUpperCase(">aaaaaaaaaaaaaaaa1aaaaaaaaa--a"[i]) then IsUpperLowerPair(">aaaaaaaaaaaaaaaa1aaaaaaaaa--a"[i], r0[i]) else r0[i] == ">aaaaaaaaaaaaaaaa1aaaaaaaaa--a"[i];
}
method {:test} Test29() {
var r0 := ToLowercase("7aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"7aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"7aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("7aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("7aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "7aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test30() {
var r0 := ToLowercase("\U{BF74}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{BF74}aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{BF74}aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("\U{BF74}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{BF74}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{BF74}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToLowercase("\U{0013}aaaaaaaaaaaaaaaa\0aaaa\U{0001}aaaa\U{0002}");
expect |r0| == |"\U{0013}aaaaaaaaaaaaaaaa\0aaaa\U{0001}aaaa\U{0002}"|;
expect forall i :: 0 <= i < |"\U{0013}aaaaaaaaaaaaaaaa\0aaaa\U{0001}aaaa\U{0002}"| ==> if IsUpperCase("\U{0013}aaaaaaaaaaaaaaaa\0aaaa\U{0001}aaaa\U{0002}"[i]) then IsUpperLowerPair("\U{0013}aaaaaaaaaaaaaaaa\0aaaa\U{0001}aaaa\U{0002}"[i], r0[i]) else r0[i] == "\U{0013}aaaaaaaaaaaaaaaa\0aaaa\U{0001}aaaa\U{0002}"[i];
}

// REPEAT 8 - TIME: 21.9574646 s

method {:test} Test32() {
var r0 := ToLowercase("%aaaaaaaaaaaaaaaaaaaa -aaaa2");
expect |r0| == |"%aaaaaaaaaaaaaaaaaaaa -aaaa2"|;
expect forall i :: 0 <= i < |"%aaaaaaaaaaaaaaaaaaaa -aaaa2"| ==> if IsUpperCase("%aaaaaaaaaaaaaaaaaaaa -aaaa2"[i]) then IsUpperLowerPair("%aaaaaaaaaaaaaaaaaaaa -aaaa2"[i], r0[i]) else r0[i] == "%aaaaaaaaaaaaaaaaaaaa -aaaa2"[i];
}
method {:test} Test33() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test34() {
var r0 := ToLowercase(":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase(":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair(":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == ":aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToLowercase("a\U{001A}aaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"a\U{001A}aaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"a\U{001A}aaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("a\U{001A}aaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("a\U{001A}aaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "a\U{001A}aaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 9 - TIME: 25.0025022 s

method {:test} Test36() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test38() {
var r0 := ToLowercase("\U{0019}aaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0019}aaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0019}aaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("\U{0019}aaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0019}aaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0019}aaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test39() {
var r0 := ToLowercase("aaaaaaaaaaaaaaa\U{0010}aaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaa\U{0010}aaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaa\U{0010}aaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaa\U{0010}aaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaa\U{0010}aaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaa\U{0010}aaaaaaaa"[i];
}

// REPEAT 10 - TIME: 28.0303894 s

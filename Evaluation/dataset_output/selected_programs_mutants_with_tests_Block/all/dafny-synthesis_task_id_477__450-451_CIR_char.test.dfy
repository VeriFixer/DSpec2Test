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
method {:test} Test3() {
var r0 := ToLowercase("@");
expect |r0| == |"@"|;
expect forall i :: 0 <= i < |"@"| ==> if IsUpperCase("@"[i]) then IsUpperLowerPair("@"[i], r0[i]) else r0[i] == "@"[i];
}

// REPEAT 1 - TIME: 4.0261888 s

method {:test} Test4() {
var r0 := ToLowercase("&");
expect |r0| == |"&"|;
expect forall i :: 0 <= i < |"&"| ==> if IsUpperCase("&"[i]) then IsUpperLowerPair("&"[i], r0[i]) else r0[i] == "&"[i];
}
method {:test} Test5() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}
method {:test} Test6() {
var r0 := ToLowercase("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW");
expect |r0| == |"aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"|;
expect forall i :: 0 <= i < |"aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"| ==> if IsUpperCase("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i]) then IsUpperLowerPair("aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i], r0[i]) else r0[i] == "aa\U{0014}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW"[i];
}
method {:test} Test7() {
var r0 := ToLowercase("\U{001A}a");
expect |r0| == |"\U{001A}a"|;
expect forall i :: 0 <= i < |"\U{001A}a"| ==> if IsUpperCase("\U{001A}a"[i]) then IsUpperLowerPair("\U{001A}a"[i], r0[i]) else r0[i] == "\U{001A}a"[i];
}

// REPEAT 2 - TIME: 6.6043239 s

method {:test} Test8() {
var r0 := ToLowercase(" a\U{000F}");
expect |r0| == |" a\U{000F}"|;
expect forall i :: 0 <= i < |" a\U{000F}"| ==> if IsUpperCase(" a\U{000F}"[i]) then IsUpperLowerPair(" a\U{000F}"[i], r0[i]) else r0[i] == " a\U{000F}"[i];
}
method {:test} Test9() {
var r0 := ToLowercase("%aaaaaa\U{0003}aaaaaa>");
expect |r0| == |"%aaaaaa\U{0003}aaaaaa>"|;
expect forall i :: 0 <= i < |"%aaaaaa\U{0003}aaaaaa>"| ==> if IsUpperCase("%aaaaaa\U{0003}aaaaaa>"[i]) then IsUpperLowerPair("%aaaaaa\U{0003}aaaaaa>"[i], r0[i]) else r0[i] == "%aaaaaa\U{0003}aaaaaa>"[i];
}
method {:test} Test10() {
var r0 := ToLowercase("\n");
expect |r0| == |"\n"|;
expect forall i :: 0 <= i < |"\n"| ==> if IsUpperCase("\n"[i]) then IsUpperLowerPair("\n"[i], r0[i]) else r0[i] == "\n"[i];
}
method {:test} Test11() {
var r0 := ToLowercase(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0");
expect |r0| == |" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"|;
expect forall i :: 0 <= i < |" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"| ==> if IsUpperCase(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i]) then IsUpperLowerPair(" a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i], r0[i]) else r0[i] == " a\U{0001}aaaaaaaaaaaaaaaaaaaaa\0"[i];
}

// REPEAT 3 - TIME: 9.3914155 s

method {:test} Test12() {
var r0 := ToLowercase("4@a");
expect |r0| == |"4@a"|;
expect forall i :: 0 <= i < |"4@a"| ==> if IsUpperCase("4@a"[i]) then IsUpperLowerPair("4@a"[i], r0[i]) else r0[i] == "4@a"[i];
}
method {:test} Test13() {
var r0 := ToLowercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test15() {
var r0 := ToLowercase(" 1aaaaaaaaaa\0aaaaaa\U{0001}");
expect |r0| == |" 1aaaaaaaaaa\0aaaaaa\U{0001}"|;
expect forall i :: 0 <= i < |" 1aaaaaaaaaa\0aaaaaa\U{0001}"| ==> if IsUpperCase(" 1aaaaaaaaaa\0aaaaaa\U{0001}"[i]) then IsUpperLowerPair(" 1aaaaaaaaaa\0aaaaaa\U{0001}"[i], r0[i]) else r0[i] == " 1aaaaaaaaaa\0aaaaaa\U{0001}"[i];
}

// REPEAT 4 - TIME: 11.5449476 s

method {:test} Test16() {
var r0 := ToLowercase(",a-aaaaaaa2aaaaaaaaa>");
expect |r0| == |",a-aaaaaaa2aaaaaaaaa>"|;
expect forall i :: 0 <= i < |",a-aaaaaaa2aaaaaaaaa>"| ==> if IsUpperCase(",a-aaaaaaa2aaaaaaaaa>"[i]) then IsUpperLowerPair(",a-aaaaaaa2aaaaaaaaa>"[i], r0[i]) else r0[i] == ",a-aaaaaaa2aaaaaaaaa>"[i];
}
method {:test} Test17() {
var r0 := ToLowercase("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<");
expect |r0| == |"\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"|;
expect forall i :: 0 <= i < |"\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"| ==> if IsUpperCase("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i]) then IsUpperLowerPair("\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i], r0[i]) else r0[i] == "\U{0010}aaaaaaaaa\U{0007}aaaaa>aaa\U{0005}aa<"[i];
}
method {:test} Test18() {
var r0 := ToLowercase("<aaa");
expect |r0| == |"<aaa"|;
expect forall i :: 0 <= i < |"<aaa"| ==> if IsUpperCase("<aaa"[i]) then IsUpperLowerPair("<aaa"[i], r0[i]) else r0[i] == "<aaa"[i];
}
method {:test} Test19() {
var r0 := ToLowercase("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}");
expect |r0| == |"a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"|;
expect forall i :: 0 <= i < |"a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"| ==> if IsUpperCase("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i]) then IsUpperLowerPair("a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i], r0[i]) else r0[i] == "a\U{0013}\U{0001}aaaaaaaaaaaaaaaaaaa\U{0003}aa\ta\U{0007}aaaa\U{0005}aaaaaaaaaaaaaaa\U{000B}"[i];
}

// REPEAT 5 - TIME: 13.784973 s

method {:test} Test20() {
var r0 := ToLowercase("%aaaaaaaaaaaa=a\U{0014}");
expect |r0| == |"%aaaaaaaaaaaa=a\U{0014}"|;
expect forall i :: 0 <= i < |"%aaaaaaaaaaaa=a\U{0014}"| ==> if IsUpperCase("%aaaaaaaaaaaa=a\U{0014}"[i]) then IsUpperLowerPair("%aaaaaaaaaaaa=a\U{0014}"[i], r0[i]) else r0[i] == "%aaaaaaaaaaaa=a\U{0014}"[i];
}
method {:test} Test21() {
var r0 := ToLowercase("\U{001E}\U{001D}a");
expect |r0| == |"\U{001E}\U{001D}a"|;
expect forall i :: 0 <= i < |"\U{001E}\U{001D}a"| ==> if IsUpperCase("\U{001E}\U{001D}a"[i]) then IsUpperLowerPair("\U{001E}\U{001D}a"[i], r0[i]) else r0[i] == "\U{001E}\U{001D}a"[i];
}
method {:test} Test22() {
var r0 := ToLowercase("\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0015}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test23() {
var r0 := ToLowercase("a\U{000F}aaa\0a");
expect |r0| == |"a\U{000F}aaa\0a"|;
expect forall i :: 0 <= i < |"a\U{000F}aaa\0a"| ==> if IsUpperCase("a\U{000F}aaa\0a"[i]) then IsUpperLowerPair("a\U{000F}aaa\0a"[i], r0[i]) else r0[i] == "a\U{000F}aaa\0a"[i];
}

// REPEAT 6 - TIME: 16.1527597 s

method {:test} Test24() {
var r0 := ToLowercase(" aaa\U{000F}");
expect |r0| == |" aaa\U{000F}"|;
expect forall i :: 0 <= i < |" aaa\U{000F}"| ==> if IsUpperCase(" aaa\U{000F}"[i]) then IsUpperLowerPair(" aaa\U{000F}"[i], r0[i]) else r0[i] == " aaa\U{000F}"[i];
}
method {:test} Test25() {
var r0 := ToLowercase("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "&aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test26() {
var r0 := ToLowercase(",a\U{0007}aaa");
expect |r0| == |",a\U{0007}aaa"|;
expect forall i :: 0 <= i < |",a\U{0007}aaa"| ==> if IsUpperCase(",a\U{0007}aaa"[i]) then IsUpperLowerPair(",a\U{0007}aaa"[i], r0[i]) else r0[i] == ",a\U{0007}aaa"[i];
}
method {:test} Test27() {
var r0 := ToLowercase("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa");
expect |r0| == |"-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"|;
expect forall i :: 0 <= i < |"-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"| ==> if IsUpperCase("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i]) then IsUpperLowerPair("-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i], r0[i]) else r0[i] == "-a\U{0013}aaaaaaaaaaaaaaaaaa\U{0001}aaa\U{0008}aaaaaaaa\U{0004}aaaa\U{0006}aaa\naaaa"[i];
}

// REPEAT 7 - TIME: 18.972907 s

method {:test} Test28() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaa\U{000F}aaaaaaaaaaaaaaaaaaaaa\U{0010}aa-a"[i];
}
method {:test} Test29() {
var r0 := ToLowercase("-a-aaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"-a-aaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"-a-aaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("-a-aaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("-a-aaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "-a-aaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test30() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToLowercase("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa");
expect |r0| == |"a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"|;
expect forall i :: 0 <= i < |"a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"| ==> if IsUpperCase("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i]) then IsUpperLowerPair("a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i], r0[i]) else r0[i] == "a aaaaaaaaaaaaaaaaaaaaaaa\0aaaaaaaaaaaa\U{0002}aa\U{0004}aaaaa"[i];
}

// REPEAT 8 - TIME: 21.5902695 s

method {:test} Test32() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToLowercase("\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0010}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}

// REPEAT 9 - TIME: 24.5309797 s

method {:test} Test36() {
var r0 := ToLowercase("a2-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"a2-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"a2-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("a2-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("a2-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "a2-aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test37() {
var r0 := ToLowercase("a--aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"a--aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"a--aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("a--aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("a--aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "a--aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test38() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test39() {
var r0 := ToLowercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaa"| ==> if IsUpperCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaa"[i]) then IsUpperLowerPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa aaaaaaaaaaaaa"[i];
}

// REPEAT 10 - TIME: 27.7287788 s

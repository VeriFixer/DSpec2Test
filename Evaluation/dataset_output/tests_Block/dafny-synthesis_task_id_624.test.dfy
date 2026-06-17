predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

method {:testEntry} ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) ==> s[k] == s'[k]
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
        }
        else 
        {
            s' := s' + [s[i]];
        }
    }
    return s';
}

method {:test} Test0() {
var r0 := ToUppercase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test3() {
var r0 := ToUppercase("`");
expect |r0| == |"`"|;
expect forall i :: 0 <= i < |"`"| ==> if IsLowerCase("`"[i]) then IsLowerUpperPair("`"[i], r0[i]) else r0[i] == "`"[i];
}

// REPEAT 1 - TIME: 4.1054645 s

method {:test} Test4() {
var r0 := ToUppercase("&");
expect |r0| == |"&"|;
expect forall i :: 0 <= i < |"&"| ==> if IsLowerCase("&"[i]) then IsLowerUpperPair("&"[i], r0[i]) else r0[i] == "&"[i];
}
method {:test} Test5() {
var r0 := ToUppercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsLowerCase("aa"[i]) then IsLowerUpperPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}
method {:test} Test6() {
var r0 := ToUppercase("aaaaa\rc");
expect |r0| == |"aaaaa\rc"|;
expect forall i :: 0 <= i < |"aaaaa\rc"| ==> if IsLowerCase("aaaaa\rc"[i]) then IsLowerUpperPair("aaaaa\rc"[i], r0[i]) else r0[i] == "aaaaa\rc"[i];
}
method {:test} Test7() {
var r0 := ToUppercase(":a");
expect |r0| == |":a"|;
expect forall i :: 0 <= i < |":a"| ==> if IsLowerCase(":a"[i]) then IsLowerUpperPair(":a"[i], r0[i]) else r0[i] == ":a"[i];
}

// REPEAT 2 - TIME: 6.4972539 s

method {:test} Test8() {
var r0 := ToUppercase("Ta");
expect |r0| == |"Ta"|;
expect forall i :: 0 <= i < |"Ta"| ==> if IsLowerCase("Ta"[i]) then IsLowerUpperPair("Ta"[i], r0[i]) else r0[i] == "Ta"[i];
}
method {:test} Test9() {
var r0 := ToUppercase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else r0[i] == ""[i];
}
method {:test} Test10() {
var r0 := ToUppercase("\U{0018}");
expect |r0| == |"\U{0018}"|;
expect forall i :: 0 <= i < |"\U{0018}"| ==> if IsLowerCase("\U{0018}"[i]) then IsLowerUpperPair("\U{0018}"[i], r0[i]) else r0[i] == "\U{0018}"[i];
}
method {:test} Test11() {
var r0 := ToUppercase("\U{000C}:");
expect |r0| == |"\U{000C}:"|;
expect forall i :: 0 <= i < |"\U{000C}:"| ==> if IsLowerCase("\U{000C}:"[i]) then IsLowerUpperPair("\U{000C}:"[i], r0[i]) else r0[i] == "\U{000C}:"[i];
}

// REPEAT 3 - TIME: 8.9776397 s

method {:test} Test12() {
var r0 := ToUppercase("$a");
expect |r0| == |"$a"|;
expect forall i :: 0 <= i < |"$a"| ==> if IsLowerCase("$a"[i]) then IsLowerUpperPair("$a"[i], r0[i]) else r0[i] == "$a"[i];
}
method {:test} Test13() {
var r0 := ToUppercase("a\U{0017}<");
expect |r0| == |"a\U{0017}<"|;
expect forall i :: 0 <= i < |"a\U{0017}<"| ==> if IsLowerCase("a\U{0017}<"[i]) then IsLowerUpperPair("a\U{0017}<"[i], r0[i]) else r0[i] == "a\U{0017}<"[i];
}
method {:test} Test14() {
var r0 := ToUppercase("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0007}\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test15() {
var r0 := ToUppercase("(");
expect |r0| == |"("|;
expect forall i :: 0 <= i < |"("| ==> if IsLowerCase("("[i]) then IsLowerUpperPair("("[i], r0[i]) else r0[i] == "("[i];
}

// REPEAT 4 - TIME: 11.4821922 s

method {:test} Test16() {
var r0 := ToUppercase("(aa\\");
expect |r0| == |"(aa\\"|;
expect forall i :: 0 <= i < |"(aa\\"| ==> if IsLowerCase("(aa\\"[i]) then IsLowerUpperPair("(aa\\"[i], r0[i]) else r0[i] == "(aa\\"[i];
}
method {:test} Test17() {
var r0 := ToUppercase("\U{0018}aW");
expect |r0| == |"\U{0018}aW"|;
expect forall i :: 0 <= i < |"\U{0018}aW"| ==> if IsLowerCase("\U{0018}aW"[i]) then IsLowerUpperPair("\U{0018}aW"[i], r0[i]) else r0[i] == "\U{0018}aW"[i];
}
method {:test} Test18() {
var r0 := ToUppercase("\U{0015}aaa");
expect |r0| == |"\U{0015}aaa"|;
expect forall i :: 0 <= i < |"\U{0015}aaa"| ==> if IsLowerCase("\U{0015}aaa"[i]) then IsLowerUpperPair("\U{0015}aaa"[i], r0[i]) else r0[i] == "\U{0015}aaa"[i];
}
method {:test} Test19() {
var r0 := ToUppercase("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}");
expect |r0| == |"\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"|;
expect forall i :: 0 <= i < |"\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"| ==> if IsLowerCase("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i]) then IsLowerUpperPair("\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i], r0[i]) else r0[i] == "\U{0017}\U{0004}aaaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaa\U{0004}"[i];
}

// REPEAT 5 - TIME: 13.3760415 s

method {:test} Test20() {
var r0 := ToUppercase("T");
expect |r0| == |"T"|;
expect forall i :: 0 <= i < |"T"| ==> if IsLowerCase("T"[i]) then IsLowerUpperPair("T"[i], r0[i]) else r0[i] == "T"[i];
}
method {:test} Test21() {
var r0 := ToUppercase("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Qa<aaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test22() {
var r0 := ToUppercase(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair(">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == ">a\U{0007}aa\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test23() {
var r0 := ToUppercase("\U{001C}_a\r\U{001B}");
expect |r0| == |"\U{001C}_a\r\U{001B}"|;
expect forall i :: 0 <= i < |"\U{001C}_a\r\U{001B}"| ==> if IsLowerCase("\U{001C}_a\r\U{001B}"[i]) then IsLowerUpperPair("\U{001C}_a\r\U{001B}"[i], r0[i]) else r0[i] == "\U{001C}_a\r\U{001B}"[i];
}

// REPEAT 6 - TIME: 15.5954263 s

method {:test} Test24() {
var r0 := ToUppercase("aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!");
expect |r0| == |"aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"|;
expect forall i :: 0 <= i < |"aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"| ==> if IsLowerCase("aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"[i]) then IsLowerUpperPair("aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"[i], r0[i]) else r0[i] == "aaaaaGaa$Qaaaaaaaaaaaaaaaaaaaaa\U{0017}!"[i];
}
method {:test} Test25() {
var r0 := ToUppercase("\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{001C}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test26() {
var r0 := ToUppercase("Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa");
expect |r0| == |"Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Kaaaaaaaaaaaaa!aaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test27() {
var r0 := ToUppercase("<aaaaa\U{0004}\U{001C}");
expect |r0| == |"<aaaaa\U{0004}\U{001C}"|;
expect forall i :: 0 <= i < |"<aaaaa\U{0004}\U{001C}"| ==> if IsLowerCase("<aaaaa\U{0004}\U{001C}"[i]) then IsLowerUpperPair("<aaaaa\U{0004}\U{001C}"[i], r0[i]) else r0[i] == "<aaaaa\U{0004}\U{001C}"[i];
}

// REPEAT 7 - TIME: 17.948449 s

method {:test} Test28() {
var r0 := ToUppercase("Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ");
expect |r0| == |"Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"|;
expect forall i :: 0 <= i < |"Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"| ==> if IsLowerCase("Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"[i]) then IsLowerUpperPair("Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"[i], r0[i]) else r0[i] == "Taaaaaaaaaaaaaaaaaaaaaaaaaa<aa\U{0017}aaaaaaQ"[i];
}
method {:test} Test29() {
var r0 := ToUppercase("Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "Gaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test30() {
var r0 := ToUppercase("\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "\U{0018}a\U{0018}aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test31() {
var r0 := ToUppercase("\U{0004}a\U{0001}\U{0003}a\U{0005}");
expect |r0| == |"\U{0004}a\U{0001}\U{0003}a\U{0005}"|;
expect forall i :: 0 <= i < |"\U{0004}a\U{0001}\U{0003}a\U{0005}"| ==> if IsLowerCase("\U{0004}a\U{0001}\U{0003}a\U{0005}"[i]) then IsLowerUpperPair("\U{0004}a\U{0001}\U{0003}a\U{0005}"[i], r0[i]) else r0[i] == "\U{0004}a\U{0001}\U{0003}a\U{0005}"[i];
}

// REPEAT 8 - TIME: 20.9554742 s

method {:test} Test32() {
var r0 := ToUppercase("aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9");
expect |r0| == |"aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"|;
expect forall i :: 0 <= i < |"aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"| ==> if IsLowerCase("aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"[i]) then IsLowerUpperPair("aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"[i], r0[i]) else r0[i] == "aaaaaaaa\U{0017}aaaaaaaaaaaaaaaaaaaaaaaQa$aaaG!9"[i];
}
method {:test} Test33() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test35() {
var r0 := ToUppercase("Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}");
expect |r0| == |"Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"|;
expect forall i :: 0 <= i < |"Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"| ==> if IsLowerCase("Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"[i]) then IsLowerUpperPair("Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"[i], r0[i]) else r0[i] == "Daaaaa\U{0001}aaaaaaaaaaaaaaaaaaaaaaaaa\U{0003}\U{000B}\U{0007}a\ta\U{0005}"[i];
}

// REPEAT 9 - TIME: 24.3565002 s

method {:test} Test36() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa&"[i];
}
method {:test} Test37() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
expect |r0| == |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"| ==> if IsLowerCase("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"[i];
}
method {:test} Test39() {
var r0 := ToUppercase("aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}");
expect |r0| == |"aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"|;
expect forall i :: 0 <= i < |"aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"| ==> if IsLowerCase("aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"[i]) then IsLowerUpperPair("aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"[i], r0[i]) else r0[i] == "aaaaaaaaaaaaaaaa$aaaaaaaaaaaaaaaaa\U{0001}aaaa\U{0003}a\U{0005}"[i];
}

// REPEAT 10 - TIME: 27.333884 s

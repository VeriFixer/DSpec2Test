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

// REPEAT 1 - TIME: 3.5843891 s

method {:test} Test1() {
var r0 := ToLowercase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 2 - TIME: 4.8990427 s

method {:test} Test2() {
var r0 := ToLowercase("a@a");
expect |r0| == |"a@a"|;
expect forall i :: 0 <= i < |"a@a"| ==> if IsUpperCase("a@a"[i]) then IsUpperLowerPair("a@a"[i], r0[i]) else r0[i] == "a@a"[i];
}

// REPEAT 3 - TIME: 5.9855271 s

method {:test} Test3() {
var r0 := ToLowercase("0\U{000F}a");
expect |r0| == |"0\U{000F}a"|;
expect forall i :: 0 <= i < |"0\U{000F}a"| ==> if IsUpperCase("0\U{000F}a"[i]) then IsUpperLowerPair("0\U{000F}a"[i], r0[i]) else r0[i] == "0\U{000F}a"[i];
}

// REPEAT 4 - TIME: 7.1326198 s

method {:test} Test4() {
var r0 := ToLowercase("0\U{000F}");
expect |r0| == |"0\U{000F}"|;
expect forall i :: 0 <= i < |"0\U{000F}"| ==> if IsUpperCase("0\U{000F}"[i]) then IsUpperLowerPair("0\U{000F}"[i], r0[i]) else r0[i] == "0\U{000F}"[i];
}

// REPEAT 5 - TIME: 8.1598955 s

method {:test} Test5() {
var r0 := ToLowercase("\U{000F}aaa");
expect |r0| == |"\U{000F}aaa"|;
expect forall i :: 0 <= i < |"\U{000F}aaa"| ==> if IsUpperCase("\U{000F}aaa"[i]) then IsUpperLowerPair("\U{000F}aaa"[i], r0[i]) else r0[i] == "\U{000F}aaa"[i];
}

// REPEAT 6 - TIME: 9.116624 s

method {:test} Test6() {
var r0 := ToLowercase("1a");
expect |r0| == |"1a"|;
expect forall i :: 0 <= i < |"1a"| ==> if IsUpperCase("1a"[i]) then IsUpperLowerPair("1a"[i], r0[i]) else r0[i] == "1a"[i];
}

// REPEAT 7 - TIME: 10.0564107 s

method {:test} Test7() {
var r0 := ToLowercase("\t\n[a");
expect |r0| == |"\t\n[a"|;
expect forall i :: 0 <= i < |"\t\n[a"| ==> if IsUpperCase("\t\n[a"[i]) then IsUpperLowerPair("\t\n[a"[i], r0[i]) else r0[i] == "\t\n[a"[i];
}

// REPEAT 8 - TIME: 10.8279469 s

method {:test} Test8() {
var r0 := ToLowercase("9\U{0001}");
expect |r0| == |"9\U{0001}"|;
expect forall i :: 0 <= i < |"9\U{0001}"| ==> if IsUpperCase("9\U{0001}"[i]) then IsUpperLowerPair("9\U{0001}"[i], r0[i]) else r0[i] == "9\U{0001}"[i];
}

// REPEAT 9 - TIME: 11.7378888 s

method {:test} Test9() {
var r0 := ToLowercase("\U{0013}a");
expect |r0| == |"\U{0013}a"|;
expect forall i :: 0 <= i < |"\U{0013}a"| ==> if IsUpperCase("\U{0013}a"[i]) then IsUpperLowerPair("\U{0013}a"[i], r0[i]) else r0[i] == "\U{0013}a"[i];
}

// REPEAT 10 - TIME: 12.6589944 s

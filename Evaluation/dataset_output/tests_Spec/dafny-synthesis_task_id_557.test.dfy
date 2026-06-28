predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

method {:testEntry} ToggleCase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
{
    var s' : string := [];
    for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |s'| == i
    invariant forall k :: 0 <= k < i &&  IsLowerCase(s[k]) ==> IsLowerUpperPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i &&  IsUpperCase(s[k]) ==> IsUpperLowerPair(s[k], s'[k])
    invariant forall k :: 0 <= k < i && !IsLowerCase(s[k]) && !IsUpperCase(s[k]) ==> s[k] == s'[k]
    {
        if IsLowerCase(s[i])
        {
            s' := s' + [ShiftMinus32(s[i])];
        }
        else if IsUpperCase(s[i])
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
var r0 := ToggleCase("");
expect |r0| == |""|;
expect forall i :: 0 <= i < |""| ==> if IsLowerCase(""[i]) then IsLowerUpperPair(""[i], r0[i]) else if IsUpperCase(""[i]) then IsUpperLowerPair(""[i], r0[i]) else r0[i] == ""[i];
}

// REPEAT 1 - TIME: 3.2485043 s

method {:test} Test1() {
var r0 := ToggleCase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}

// REPEAT 2 - TIME: 4.4640256 s

method {:test} Test2() {
var r0 := ToggleCase("an");
expect |r0| == |"an"|;
expect forall i :: 0 <= i < |"an"| ==> if IsLowerCase("an"[i]) then IsLowerUpperPair("an"[i], r0[i]) else if IsUpperCase("an"[i]) then IsUpperLowerPair("an"[i], r0[i]) else r0[i] == "an"[i];
}

// REPEAT 3 - TIME: 5.6388717 s

method {:test} Test3() {
var r0 := ToggleCase("a@a");
expect |r0| == |"a@a"|;
expect forall i :: 0 <= i < |"a@a"| ==> if IsLowerCase("a@a"[i]) then IsLowerUpperPair("a@a"[i], r0[i]) else if IsUpperCase("a@a"[i]) then IsUpperLowerPair("a@a"[i], r0[i]) else r0[i] == "a@a"[i];
}

// REPEAT 4 - TIME: 6.7780361 s

method {:test} Test4() {
var r0 := ToggleCase("a\U{001A}aa");
expect |r0| == |"a\U{001A}aa"|;
expect forall i :: 0 <= i < |"a\U{001A}aa"| ==> if IsLowerCase("a\U{001A}aa"[i]) then IsLowerUpperPair("a\U{001A}aa"[i], r0[i]) else if IsUpperCase("a\U{001A}aa"[i]) then IsUpperLowerPair("a\U{001A}aa"[i], r0[i]) else r0[i] == "a\U{001A}aa"[i];
}

// REPEAT 5 - TIME: 7.748898 s

method {:test} Test5() {
var r0 := ToggleCase("\U{000F}a");
expect |r0| == |"\U{000F}a"|;
expect forall i :: 0 <= i < |"\U{000F}a"| ==> if IsLowerCase("\U{000F}a"[i]) then IsLowerUpperPair("\U{000F}a"[i], r0[i]) else if IsUpperCase("\U{000F}a"[i]) then IsUpperLowerPair("\U{000F}a"[i], r0[i]) else r0[i] == "\U{000F}a"[i];
}

// REPEAT 6 - TIME: 8.8121912 s

method {:test} Test6() {
var r0 := ToggleCase("1g[");
expect |r0| == |"1g["|;
expect forall i :: 0 <= i < |"1g["| ==> if IsLowerCase("1g["[i]) then IsLowerUpperPair("1g["[i], r0[i]) else if IsUpperCase("1g["[i]) then IsUpperLowerPair("1g["[i], r0[i]) else r0[i] == "1g["[i];
}

// REPEAT 7 - TIME: 9.7732025 s

method {:test} Test7() {
var r0 := ToggleCase("d\U{001B}aa");
expect |r0| == |"d\U{001B}aa"|;
expect forall i :: 0 <= i < |"d\U{001B}aa"| ==> if IsLowerCase("d\U{001B}aa"[i]) then IsLowerUpperPair("d\U{001B}aa"[i], r0[i]) else if IsUpperCase("d\U{001B}aa"[i]) then IsUpperLowerPair("d\U{001B}aa"[i], r0[i]) else r0[i] == "d\U{001B}aa"[i];
}

// REPEAT 8 - TIME: 10.619115 s

method {:test} Test8() {
var r0 := ToggleCase(">\U{0005}");
expect |r0| == |">\U{0005}"|;
expect forall i :: 0 <= i < |">\U{0005}"| ==> if IsLowerCase(">\U{0005}"[i]) then IsLowerUpperPair(">\U{0005}"[i], r0[i]) else if IsUpperCase(">\U{0005}"[i]) then IsUpperLowerPair(">\U{0005}"[i], r0[i]) else r0[i] == ">\U{0005}"[i];
}

// REPEAT 9 - TIME: 11.3199421 s

method {:test} Test9() {
var r0 := ToggleCase("0\U{001A}1a");
expect |r0| == |"0\U{001A}1a"|;
expect forall i :: 0 <= i < |"0\U{001A}1a"| ==> if IsLowerCase("0\U{001A}1a"[i]) then IsLowerUpperPair("0\U{001A}1a"[i], r0[i]) else if IsUpperCase("0\U{001A}1a"[i]) then IsUpperLowerPair("0\U{001A}1a"[i], r0[i]) else r0[i] == "0\U{001A}1a"[i];
}

// REPEAT 10 - TIME: 12.1408674 s

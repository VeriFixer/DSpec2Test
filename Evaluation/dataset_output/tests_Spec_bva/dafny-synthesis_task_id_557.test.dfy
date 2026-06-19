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
method {:test} Test2() {
var r0 := ToggleCase("a");
expect |r0| == |"a"|;
expect forall i :: 0 <= i < |"a"| ==> if IsLowerCase("a"[i]) then IsLowerUpperPair("a"[i], r0[i]) else if IsUpperCase("a"[i]) then IsUpperLowerPair("a"[i], r0[i]) else r0[i] == "a"[i];
}
method {:test} Test3() {
var r0 := ToggleCase("aa");
expect |r0| == |"aa"|;
expect forall i :: 0 <= i < |"aa"| ==> if IsLowerCase("aa"[i]) then IsLowerUpperPair("aa"[i], r0[i]) else if IsUpperCase("aa"[i]) then IsUpperLowerPair("aa"[i], r0[i]) else r0[i] == "aa"[i];
}

// REPEAT 1 - TIME: 7.4905024 s

method {:test} Test10() {
var r0 := ToggleCase("d&");
expect |r0| == |"d&"|;
expect forall i :: 0 <= i < |"d&"| ==> if IsLowerCase("d&"[i]) then IsLowerUpperPair("d&"[i], r0[i]) else if IsUpperCase("d&"[i]) then IsUpperLowerPair("d&"[i], r0[i]) else r0[i] == "d&"[i];
}

// REPEAT 2 - TIME: 8.4469795 s

method {:test} Test11() {
var r0 := ToggleCase("&@a");
expect |r0| == |"&@a"|;
expect forall i :: 0 <= i < |"&@a"| ==> if IsLowerCase("&@a"[i]) then IsLowerUpperPair("&@a"[i], r0[i]) else if IsUpperCase("&@a"[i]) then IsUpperLowerPair("&@a"[i], r0[i]) else r0[i] == "&@a"[i];
}

// REPEAT 3 - TIME: 9.2086675 s

method {:test} Test12() {
var r0 := ToggleCase("{\U{001A}1");
expect |r0| == |"{\U{001A}1"|;
expect forall i :: 0 <= i < |"{\U{001A}1"| ==> if IsLowerCase("{\U{001A}1"[i]) then IsLowerUpperPair("{\U{001A}1"[i], r0[i]) else if IsUpperCase("{\U{001A}1"[i]) then IsUpperLowerPair("{\U{001A}1"[i], r0[i]) else r0[i] == "{\U{001A}1"[i];
}

// REPEAT 4 - TIME: 10.0677146 s

method {:test} Test13() {
var r0 := ToggleCase(" aaaaaaaaaaaaaaaaaaaaaaa aa-");
expect |r0| == |" aaaaaaaaaaaaaaaaaaaaaaa aa-"|;
expect forall i :: 0 <= i < |" aaaaaaaaaaaaaaaaaaaaaaa aa-"| ==> if IsLowerCase(" aaaaaaaaaaaaaaaaaaaaaaa aa-"[i]) then IsLowerUpperPair(" aaaaaaaaaaaaaaaaaaaaaaa aa-"[i], r0[i]) else if IsUpperCase(" aaaaaaaaaaaaaaaaaaaaaaa aa-"[i]) then IsUpperLowerPair(" aaaaaaaaaaaaaaaaaaaaaaa aa-"[i], r0[i]) else r0[i] == " aaaaaaaaaaaaaaaaaaaaaaa aa-"[i];
}

// REPEAT 5 - TIME: 10.8069902 s

method {:test} Test14() {
var r0 := ToggleCase(" \U{000F}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000F}");
expect |r0| == |" \U{000F}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"|;
expect forall i :: 0 <= i < |" \U{000F}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"| ==> if IsLowerCase(" \U{000F}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i]) then IsLowerUpperPair(" \U{000F}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i], r0[i]) else if IsUpperCase(" \U{000F}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i]) then IsUpperLowerPair(" \U{000F}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i], r0[i]) else r0[i] == " \U{000F}aaaaaaaaaaaaaaaaaaaaaaaaaa\U{000F}"[i];
}

// REPEAT 6 - TIME: 11.5701846 s

method {:test} Test15() {
var r0 := ToggleCase("!>aaaaa\U{0013}aaaaaa2");
expect |r0| == |"!>aaaaa\U{0013}aaaaaa2"|;
expect forall i :: 0 <= i < |"!>aaaaa\U{0013}aaaaaa2"| ==> if IsLowerCase("!>aaaaa\U{0013}aaaaaa2"[i]) then IsLowerUpperPair("!>aaaaa\U{0013}aaaaaa2"[i], r0[i]) else if IsUpperCase("!>aaaaa\U{0013}aaaaaa2"[i]) then IsUpperLowerPair("!>aaaaa\U{0013}aaaaaa2"[i], r0[i]) else r0[i] == "!>aaaaa\U{0013}aaaaaa2"[i];
}

// REPEAT 7 - TIME: 12.3643302 s

method {:test} Test16() {
var r0 := ToggleCase("-\U{0010}aaaaaaaaaaa a ");
expect |r0| == |"-\U{0010}aaaaaaaaaaa a "|;
expect forall i :: 0 <= i < |"-\U{0010}aaaaaaaaaaa a "| ==> if IsLowerCase("-\U{0010}aaaaaaaaaaa a "[i]) then IsLowerUpperPair("-\U{0010}aaaaaaaaaaa a "[i], r0[i]) else if IsUpperCase("-\U{0010}aaaaaaaaaaa a "[i]) then IsUpperLowerPair("-\U{0010}aaaaaaaaaaa a "[i], r0[i]) else r0[i] == "-\U{0010}aaaaaaaaaaa a "[i];
}

// REPEAT 8 - TIME: 13.0478391 s

method {:test} Test17() {
var r0 := ToggleCase("\U{000F} aaaaaaaa aaaaaaaaaaaa--");
expect |r0| == |"\U{000F} aaaaaaaa aaaaaaaaaaaa--"|;
expect forall i :: 0 <= i < |"\U{000F} aaaaaaaa aaaaaaaaaaaa--"| ==> if IsLowerCase("\U{000F} aaaaaaaa aaaaaaaaaaaa--"[i]) then IsLowerUpperPair("\U{000F} aaaaaaaa aaaaaaaaaaaa--"[i], r0[i]) else if IsUpperCase("\U{000F} aaaaaaaa aaaaaaaaaaaa--"[i]) then IsUpperLowerPair("\U{000F} aaaaaaaa aaaaaaaaaaaa--"[i], r0[i]) else r0[i] == "\U{000F} aaaaaaaa aaaaaaaaaaaa--"[i];
}

// REPEAT 9 - TIME: 13.8199725 s

method {:test} Test18() {
var r0 := ToggleCase("\U{0014}?aaa\U{0003}a(a\U{0019}aaa\U{0007}");
expect |r0| == |"\U{0014}?aaa\U{0003}a(a\U{0019}aaa\U{0007}"|;
expect forall i :: 0 <= i < |"\U{0014}?aaa\U{0003}a(a\U{0019}aaa\U{0007}"| ==> if IsLowerCase("\U{0014}?aaa\U{0003}a(a\U{0019}aaa\U{0007}"[i]) then IsLowerUpperPair("\U{0014}?aaa\U{0003}a(a\U{0019}aaa\U{0007}"[i], r0[i]) else if IsUpperCase("\U{0014}?aaa\U{0003}a(a\U{0019}aaa\U{0007}"[i]) then IsUpperLowerPair("\U{0014}?aaa\U{0003}a(a\U{0019}aaa\U{0007}"[i], r0[i]) else r0[i] == "\U{0014}?aaa\U{0003}a(a\U{0019}aaa\U{0007}"[i];
}

// REPEAT 10 - TIME: 14.6525977 s
